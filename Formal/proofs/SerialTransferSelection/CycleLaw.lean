import proofs.SerialTransferSelection.CycleOutcome
import proofs.SerialTransferSelection.BatchService

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

abbrev CycleBatchState (N M : ℕ) (zL zH : ℝ) (s : ReadyPopulation N M zL zH) :=
  StoppedPopulation (phaseActiveDomain N M (membrane s.val.live) zL zH)

noncomputable def cycleBatchModel (N M : ℕ) (zL zH γ : ℝ) (hγ : 0 ≤ γ)
    (s : ReadyPopulation N M zL zH) :=
  phaseStoppedModel γ hγ (4*membrane s.val.live) N (membrane s.val.live) zL zH
    (phaseActiveDomain N M (membrane s.val.live) zL zH)

def cycleBatchGoodSet (N M J : ℕ) (zL zH : ℝ) (s : ReadyPopulation N M zL zH) :
    Set (CycleBatchState N M zL zH s × Fin (J+1)) :=
  {x | x.1 ∈ phaseBatchGoodSet N (membrane s.val.live)
    (ancestralMembrane true s.val.live) (ancestralMembrane false s.val.live) zL zH
    (phaseActiveDomain N M (membrane s.val.live) zL zH) ∧ x.2.val < J}

variable (N M JB JR : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (s : ReadyPopulation N M zL zH)
  (qr : NNReal) (hqr : 0 < (qr : ℝ))
  (hclockr : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr)

/-- The continuation on successful source endpoints. The complementary branch is
the analytical failure quotient, with its full original probability mass. -/
noncomputable def cycleContinuation
    (x : CycleBatchState N M zL zH s × Fin (JB+1)) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) := by
  classical
  exact if hx : x ∈ cycleBatchGoodSet N M JB zL zH s then by
    have hg := phase_good_transfer_inputs N M (by omega) hM zL zH s.val
      (readyPopulation_ready N M zL zH s) 0 (by intro tag; simp) x.1 hx.1
    exact transferRecoveryLaw N M JR hN zL zH hzL hzH (physicalState N x.1)
      hg.2.1 hg.2.2.2.1 hg.2.2.2.2.2 qr hqr hclockr
  else FiniteLaw.pure none

noncomputable def cycleStart : CycleBatchState N M zL zH s :=
  .inl ⟨s.val,phase_ready_mem_domain N M hN hM zL zH hzL hzH s.val
    (readyPopulation_ready N M zL zH s)⟩

/-- Literal batch, uniform intact sampling, fixed-time resident recovery, and
refill. Quota/chemical failures are retained, without conditional normalization. -/
noncomputable def sourceCycleLaw (γ : ℝ) (hγ : 0 ≤ γ)
    (qb t : NNReal) (hqb : 0 < (qb : ℝ))
    (hclockb : ∀ x, (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb) :
    FiniteLaw (Option (ReadyPopulation N M zL zH)) := by
  classical
  exact (poissonLaw
    ((serviceCounterModel (cycleBatchModel N M zL zH γ hγ s) JB).uniformize qb hqb
      (fun x => hclockb x.1)) (qb*t) (cycleStart N M hN hM zL zH hzL hzH s,0)).bind
    (cycleContinuation N M JB JR hN hM zL zH hzL hzH s qr hqr hclockr)

end SerialTransferSelection

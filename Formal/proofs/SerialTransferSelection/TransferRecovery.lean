import proofs.SerialTransferSelection.SelectedRecovery
import proofs.SerialTransferSelection.TransferJointProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy CoreCouplingCAC Set

def transferReadyRelation (N M : ℕ) (zL zH : ℝ) (s : PopulationState) (p ε : ℝ)
    (y : ReadyPopulation N M zL zH) : Prop :=
  (∀ b, 0 < ancestralCount b y.val.live ∧
    (1-ε)*p/16 ≤ (ancestralCount b y.val.live : ℝ)/(M : ℝ)) ∧
  Real.log (ancestralMembrane true s.live)-Real.log (ancestralMembrane false s.live)-
    Real.log ((1+ε)/(1-ε)) ≤
    Real.log (ancestralMembrane true y.val.live)-Real.log (ancestralMembrane false y.val.live)

theorem transfer_preserved_ready_relation (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (zL zH : ℝ) (s : PopulationState) (hL : 2 ≤ s.live.length) (hM : M ≤ s.live.length)
    (hcap : s.live.length ≤ 8*M) (hv : ValidVolumes N s)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : ∀ tag, (N : ℝ)*p*M ≤ ancestralMembrane tag s.live)
    (S : TransferSubset s.live.length M) (hg : S ∈ ancestralTransferGoodSet N M s hM ε)
    (y : ReadyPopulation N M zL zH) (hy : selectedAncestryPreserved N M zL zH s S y) :
    transferReadyRelation N M zL zH s p ε y := by
  constructor
  · intro b
    rw [(hy b).1]
    exact transfer_count_frequency_floor N M hN hMpos b s (by omega) hM hcap hv p ε hp
      hε.le hε1 (hB b) S (hg b)
  · rw [(hy true).2,(hy false).2]
    have hpos (b : Bool) : 0 < ancestralMembrane b s.live := by
      have h := (by positivity : (0 : ℝ) < (N : ℝ)*p*M).trans_le (hB b)
      exact_mod_cast h
    exact transfer_size_odds_loss N M hN hMpos s (by omega) hM ε hε.le hε1
      (hpos true) (hpos false) S hg

theorem finiteLaw_successful_mono {α : Type*} [Fintype α] (μ : FiniteLaw (Option α))
    (R S : α → Prop) (h : ∀ x, R x → S x) :
    μ.expect (FiniteKernel.eventIndicator (successfulOutput R)) ≤
      μ.expect (FiniteKernel.eventIndicator (successfulOutput S)) := by
  classical
  apply μ.expect_mono
  intro x
  cases x with
  | none => simp [FiniteKernel.eventIndicator,successfulOutput]
  | some x =>
    by_cases hr : R x
    · simp [FiniteKernel.eventIndicator,successfulOutput,hr,h x hr]
    · by_cases hs : S x <;> simp [FiniteKernel.eventIndicator,successfulOutput,hr,hs]

variable (N M J : ℕ) (hN : 1 ≤ N) (zL zH : ℝ)
  (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
  (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
  (s : PopulationState) (hM : M ≤ s.live.length) (hv : ValidVolumes N s)
  (he : ∀ c ∈ s.live, cellEnergy zL zH c < 8*innerEnergy)
  (q : NNReal) (hq : 0 < (q : ℝ))
  (hclock : ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ q)

/-- Every uniformly sampled intact subset receives literal recovery; the law has
no branch inspecting whether the sample has favorable ancestry totals. -/
noncomputable def transferRecoveryLaw : FiniteLaw (Option (ReadyPopulation N M zL zH)) :=
  (uniformTransferLaw s.live.length M hM).bind
    (selectedRecoveryLaw N M J hN zL zH hzL hzH s hv he q hq hclock)

theorem transferRecoveryLaw_probability
    (hsL : Stationary sourceRates (lift sourceRates zL))
    (hsH : Stationary sourceRates (lift sourceRates zH))
    (hlarge : (140000000000000000000 : ℝ) ≤ N) (hJ : 0 < J)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (hMpos : 0 < M) (hL : 2 ≤ s.live.length) (hcap : s.live.length ≤ 8*M)
    (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hε1 : ε < 1)
    (hB : ∀ tag, (N : ℝ)*p*M ≤ ancestralMembrane tag s.live) :
    1-(32/(ε^2*p*(M : ℝ))+(M : ℝ)*(recoveryError ((N : ℝ)*localAlpha*innerEnergy)+5376*(q : ℝ)/J)) ≤
      (transferRecoveryLaw N M J hN zL zH hzL hzH s hM hv he q hq hclock).expect
        (FiniteKernel.eventIndicator (successfulOutput (transferReadyRelation N M zL zH s p ε))) := by
  apply finiteLaw_joint_bind_lower _ _ (ancestralTransferGoodSet N M s hM ε) _ _ _
    (by unfold recoveryError localAlpha innerEnergy outerEnergy; positivity)
  · exact source_transfer_weighted_probability N M (by omega) hMpos s hL hM hcap hv p ε hp hε hB
  · intro S hS
    have hr := selectedRecoveryLaw_probability N M J hN zL zH hzL hzH s hv he q hq hclock
      hsL hsH hlarge hJ hk S
    exact hr.trans (finiteLaw_successful_mono _ _ _ (fun y hy =>
      transfer_preserved_ready_relation N M (by omega) hMpos zL zH s hL hM hcap hv
        p ε hp hε hε1 hB S hS y hy))

end SerialTransferSelection

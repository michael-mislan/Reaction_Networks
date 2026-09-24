import proofs.ProductiveMemory.ExtractionCycleOutcome

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false

abbrev ProductiveCycleBatchState (N M J : ℕ) (rho zL zH : ℝ) (s : ProductiveReady N M rho zL zH) :=
  ProductiveStopped (productiveActiveDomain N M (membrane s.val.population.live) J rho zL zH)

def productiveCycleBatchModel (N M J : ℕ) (rho zL zH gamma : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ gamma)
    (s : ProductiveReady N M rho zL zH) :=
  productiveStoppedModel rho gamma hr hg (4*membrane s.val.population.live) N (membrane s.val.population.live) J zL zH
    (productiveActiveDomain N M (membrane s.val.population.live) J rho zL zH)

def productiveCycleBatchGood (N M J JS : ℕ) (rho zL zH : ℝ) (s : ProductiveReady N M rho zL zH) :
    Set (ProductiveCycleBatchState N M J rho zL zH s × Fin (JS+1)) :=
  {x | x.1 ∈ productiveBatchGoodSet N (membrane s.val.population.live) J
    (ancestralMembrane true s.val.population.live) (ancestralMembrane false s.val.population.live) rho zL zH
    (productiveActiveDomain N M (membrane s.val.population.live) J rho zL zH) ∧ x.2.val < JS}

variable (N M J JS : ℕ) (hN : 1 ≤ N) (hM : 0 < M) (hlarge : recoveryCount ≤ N) (rho zL zH : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (s : ProductiveReady N M rho zL zH)

/-- Failures keep their full probability mass; successful batches retain the exact export count. -/
def productiveCycleContinuation (x : ProductiveCycleBatchState N M J rho zL zH s × Fin (JS+1)) :
    FiniteLaw (Option (ProductiveCycleResult N M J rho zL zH)) := by
  classical
  exact if hx : x ∈ productiveCycleBatchGood N M J JS rho zL zH s then by
    have hg := productive_good_transfer_inputs N M J (by omega) hM rho zL zH s.val
      (productiveReady_ready N M rho zL zH s) 0 (by intro tag; simp) x.1 hx.1
    let e : Fin J := ⟨(productivePhysical N x.1).collected,productive_good_collected N _ J _ _ rho zL zH x.1 hx.1⟩
    exact productiveRecordOutput J e (extractionTransferRecoveryLaw N M hN hlarge rho zL zH hr hzL hzH
      (productivePhysical N x.1).population hg.2.1 hg.2.2.2.1 hg.2.2.2.2.2)
  else FiniteLaw.pure none

def productiveCycleStart (hJ : 0 < J) : ProductiveCycleBatchState N M J rho zL zH s :=
  .inl ⟨s.val,productive_ready_mem_domain N M J hN hM hJ rho zL zH hr hzL hzH s.val
    (productiveReady_ready N M rho zL zH s)⟩

def productiveSourceCycleLaw (hJ : 0 < J) (gamma : ℝ) (hg : 0 ≤ gamma)
    (qb t : NNReal) (hqb : 0 < (qb:ℝ))
    (hclockb : ∀ x, (productiveCycleBatchModel N M J rho zL zH gamma (by linarith [hr.1]) hg s).total x ≤ qb) :
    FiniteLaw (Option (ProductiveCycleResult N M J rho zL zH)) := by
  classical
  exact (poissonLaw
    ((SerialTransferSelection.serviceCounterModel
      (productiveCycleBatchModel N M J rho zL zH gamma (by linarith [hr.1]) hg s) JS).uniformize qb hqb
      (fun x => hclockb x.1)) (qb*t)
      (productiveCycleStart N M J hN hM rho zL zH hr hzL hzH s hJ,0)).bind
    (productiveCycleContinuation N M J JS hN hM hlarge rho zL zH hr hzL hzH s)

end
end ProductiveMemory

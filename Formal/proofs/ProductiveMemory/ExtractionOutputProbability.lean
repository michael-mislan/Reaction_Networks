import proofs.ProductiveMemory.ExtractionOutput
import proofs.ResourceLimitedCompetition.OddsProbability

namespace ProductiveMemory
open ResourceLimitedCompetition HeritableCompositions FiniteCopy Set
open scoped NNReal
noncomputable section
set_option Elab.async false
local instance productiveOutputDecEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) := Classical.decEq _

def productiveLowOutput (N W0 : ℕ) (D : Finset ProductiveState) : Set (ProductiveStopped D) :=
  {x | (productivePhysical N x).population.resource=W0 ∧ (productivePhysical N x).collected ≤ 5*W0}

theorem productive_low_output_barrier (N W0 : ℕ) (D : Finset ProductiveState) (x : ProductiveStopped D)
    (hx : x ∈ productiveLowOutput N W0 D) : Real.exp (W0:ℝ) ≤ productiveOutputObservable N W0 x := by
  change _ ≤ Real.exp _
  apply Real.exp_le_exp.mpr
  have hE : ((productivePhysical N x).collected:ℝ) ≤ 5*(W0:ℝ) := by exact_mod_cast hx.2
  rw [hx.1]
  linarith only [hE]

theorem productive_output_probability (rho γ : ℝ) (hr : 0 ≤ rho) (hg : 0 ≤ γ)
    (hcompare : 16*γ ≤ rho) (N M W0 J : ℕ) (zL zH : ℝ)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ x, (productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH))
    (hstart : s.val.population.resource=4*W0) (hE : s.val.collected=0) :
    ((productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (productiveLowOutput N W0 (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      Real.exp (-(W0:ℝ)) := by
  classical
  have h := (productiveStoppedModel rho γ hr hg (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound q t hq hclock
      (productiveLowOutput N W0 _) (productiveOutputObservable N W0) (Real.exp (W0:ℝ)) 0
      (fun x => productive_output_value_nonneg W0 (productivePhysical N x))
      (productive_low_output_barrier N W0 _)
      (productive_output_generator rho γ hr hg hcompare N M W0 J zL zH) (.inl s)
  have hi : productiveOutputObservable N W0 (.inl s)=1 := by
    simp [productiveOutputObservable,productiveOutputValue,productivePhysical,hstart,hE]
  simp only [hi,mul_zero,add_zero] at h
  exact exp_barrier_cancel _ _ h

end
end ProductiveMemory

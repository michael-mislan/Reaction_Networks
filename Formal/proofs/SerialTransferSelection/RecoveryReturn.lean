import proofs.HeritableCompositions.RetainedRecovery
import proofs.HeritableCompositions.GrowthExit

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

/-- The C3 recovery duration pays the larger endpoint energy, not a newborn premise. -/
theorem recovery_terminal_scalar (u p W : ℝ)
    (hW : W ≤ Real.exp (8*u))
    (hbound : Real.exp u*p ≤ Real.exp (-8*u)*W+2*Real.exp (u/2)) :
    p ≤ Real.exp (-u)+2*Real.exp (-u/2) := by
  have hm := mul_le_mul_of_nonneg_left hW (Real.exp_pos (-8*u)).le
  have he : Real.exp (-8*u)*Real.exp (8*u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hm
  have he' : Real.exp u*(Real.exp (-u)+2*Real.exp (-u/2)) =
      1+2*Real.exp (u/2) := by
    rw [mul_add, mul_left_comm (Real.exp u) 2, ← Real.exp_add,
      ← Real.exp_add]
    have h1 : u + -u = 0 := by ring
    have h2 : u + -u/2 = u/2 := by ring
    rw [h1, h2, Real.exp_zero]
  have hb : Real.exp u*p ≤ Real.exp u*(Real.exp (-u)+2*Real.exp (-u/2)) := by
    rw [he']
    linarith only [hbound, hm]
  nlinarith only [hb, Real.exp_pos u]

/-- Killed terminal error on the donor's actual finite law, enlarged to energy 8a.
Exit mass is not included in this event and must be charged separately. -/
theorem endpoint_terminal_recovery (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ)
    (s : Point) (E : Point → ℝ)
    (hgen : ∀ c ∈ growthDomain N s E outerEnergy, c.2 < 2*N →
      compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration d.2 d.1 i-s i))) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration c.2 c.1 i-s i))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)))
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).total c ≤ q)
    (hk : (N : ℝ)*localAlpha*innerEnergy/672 ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N s E outerEnergy})
    (hc : c.val.2 < 2*N)
    (hendpoint : E (fun i => concentration c.val.2 c.val.1 i-s i) ≤ 8*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).uniformize q hq hclock).poissonized
      (q*5376) (FiniteKernel.eventIndicator (retainedUnrecovered N s E)) (some c) ≤
      Real.exp (-((N : ℝ)*localAlpha*innerEnergy))+
        2*Real.exp (-((N : ℝ)*localAlpha*innerEnergy)/2) := by
  classical
  let u := (N : ℝ)*localAlpha*innerEnergy
  let f := fun d : Compartment => Real.exp ((N : ℝ)*localAlpha*E (fun i => concentration d.2 d.1 i-s i))
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have hA : ∀ d ∈ retainedUnrecovered N s E, Real.exp u ≤
      activeObservable N (growthDomain N s E outerEnergy) f d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      change d.val.2 < 2*N ∧ _ at hd
      simp only [activeObservable,if_pos hd.1]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (le_of_lt hd.2) (by unfold localAlpha; positivity)
  have h := retained_affine_event γ hγ N (growthDomain N s E outerEnergy) f
    (fun _ => (Real.exp_pos _).le) (u/672) (2*Real.exp (u/2)) (by positivity) (by positivity)
    hgen q 5376 hq hclock hk (retainedUnrecovered N s E) (Real.exp u) hA c hc
  have ht : -(u/672)*(5376 : NNReal) = -8*u := by norm_num; ring
  rw [ht] at h
  apply recovery_terminal_scalar u _ (f c.val) _ h
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hendpoint
    (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
  dsimp [u]
  nlinarith only [hh]

/-- With no growth precursor every positive-rate raw reaction preserves actual size. -/
theorem zero_growth_preserves_size (c : Compartment) (r : Channel)
    (hr : 0 < propensity 0 c r) : (nextCompartment c r).2 = c.2 := by
  cases r with
  | inl r => rfl
  | inr r => simp [propensity] at hr

end SerialTransferSelection

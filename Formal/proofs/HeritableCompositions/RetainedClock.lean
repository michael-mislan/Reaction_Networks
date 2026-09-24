import proofs.HeritableCompositions.ClockTails
import proofs.HeritableCompositions.StoppedCutoff

namespace HeritableCompositions
open FiniteCopy

noncomputable def activeLiving (N : ℕ) (D : Finset Compartment) : Set (StoppedCompartment D) :=
  {c | match c with | none => False | some c => c.val.2 < 2*N}

theorem retained_late_tail (γ a : ℝ) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (N : ℕ) (D : Finset Compartment)
    (hrate : ∀ c ∈ D, c.2 < 2*N → a*(N : ℝ) ≤ γ*(c.1 2 : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : 1099/1000 ≤ a*(t : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q)
    (hk : 19*a*(N : ℝ)/400 ≤ q)
    (c : {c : Compartment // c ∈ D}) (hstart : N ≤ c.val.2) (hc : c.val.2 < 2*N) :
    ((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (activeLiving N D)) (some c) ≤ Real.exp (-(N : ℝ)/500) := by
  have hA : ∀ d ∈ activeLiving N D, Real.exp (-(N : ℝ)/20) ≤
      activeObservable N D (membraneObservable N (-1/20)) d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      change d.val.2 < 2*N at hd
      simp only [activeObservable,if_pos hd]
      apply Real.exp_le_exp.mpr
      have hm : (d.val.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hd.le
      change -(N : ℝ)/20 ≤ (-1/20)*((d.val.2 : ℝ)-(N : ℝ))
      linarith only [hm]
  have hgen (d) (hd : d ∈ D) (hm : d.2 < 2*N) :
      compartmentGenerator γ (membraneObservable N (-1/20)) d ≤
      -(19*a*(N : ℝ)/400)*membraneObservable N (-1/20) d+(19*a*(N : ℝ)/400)*0 := by
    simpa only [mul_zero,add_zero] using late_membrane_generator γ a hγ N d (hrate d hd hm)
  have h := retained_affine_event γ hγ N D (membraneObservable N (-1/20))
    (fun _ => (Real.exp_pos _).le) (19*a*(N : ℝ)/400) 0 (by positivity) (by norm_num)
    hgen q t hq hclock hk (activeLiving N D) (Real.exp (-(N : ℝ)/20)) hA c hc
  have hs : membraneObservable N (-1/20) c.val ≤ 1 := by
    have hm : (N : ℝ) ≤ c.val.2 := by exact_mod_cast hstart
    change Real.exp ((-1/20)*((c.val.2 : ℝ)-(N : ℝ))) ≤ 1
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith only [hm])
      _ = 1 := Real.exp_zero
  have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(19*a*(N : ℝ)/400)*(t : ℝ))).le
  simp only [add_zero] at h
  have hbound := h.trans (by simpa only [mul_one] using hh)
  apply (exponential_probability_cancel _ _ _ hbound).trans
  apply Real.exp_le_exp.mpr
  have htN := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith only [htN,hNr]

end HeritableCompositions

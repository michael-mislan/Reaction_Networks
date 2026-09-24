import proofs.HeritableCompositions.ClockEvents

namespace HeritableCompositions
open FiniteCopy

noncomputable def divisionRecorded (N : ℕ) (D : Finset Compartment) : Set (StoppedCompartment D) :=
  {c | match c with | none => False | some c => 2*N ≤ c.val.2}

noncomputable def stillLiving (D : Finset Compartment) : Set (StoppedCompartment D) :=
  {c | c.isSome}

theorem exponential_probability_cancel (p a b : ℝ)
    (h : Real.exp a*p ≤ Real.exp b) : p ≤ Real.exp (b-a) := by
  have he : Real.exp a*Real.exp (b-a) = Real.exp b := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he] at h
  nlinarith only [h,Real.exp_pos a]

theorem early_division_tail (γ b : ℝ) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset Compartment)
    (hrate : ∀ c ∈ D, c.2 < 2*N → γ*(c.1 2 : ℝ) ≤ 2*b*(N : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : b*(t : ℝ) ≤ 2/5)
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q)
    (c : {c : Compartment // c ∈ D}) (hstart : c.val.2=N) :
    ((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (divisionRecorded N D)) (some c) ≤ Real.exp (-(N : ℝ)/125) := by
  have hA : ∀ d ∈ divisionRecorded N D, Real.exp ((N : ℝ)/5) ≤
      growthObservable D (membraneObservable N (1/5)) 0 d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      apply Real.exp_le_exp.mpr
      have hm : (2 : ℝ)*(N : ℝ) ≤ d.val.2 := by exact_mod_cast hd
      change (N : ℝ)/5 ≤ (1/5)*((d.val.2 : ℝ)-(N : ℝ))
      linarith only [hm]
  have h := stopped_early_clock γ b hγ hb N D hrate q t hq hclock
    (divisionRecorded N D) (Real.exp ((N : ℝ)/5)) hA c
  have hs : membraneObservable N (1/5) c.val=1 := by simp [membraneObservable,hstart]
  rw [hs,mul_one] at h
  have hbtime : (12*b*(N : ℝ)/25)*(t : ℝ)-(N : ℝ)/5 ≤ -(N : ℝ)/125 := by
    have hh := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    nlinarith only [hh]
  exact (exponential_probability_cancel _ _ _ h).trans (Real.exp_le_exp.mpr hbtime)

theorem late_division_tail (γ a : ℝ) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (N : ℕ) (D : Finset Compartment) (hD : ∀ c ∈ D, c.2 < 2*N)
    (hrate : ∀ c ∈ D, a*(N : ℝ) ≤ γ*(c.1 2 : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : a*(t : ℝ)=11/10)
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q)
    (hk : 19*a*(N : ℝ)/400 ≤ q)
    (c : {c : Compartment // c ∈ D}) (hstart : c.val.2=N) :
    ((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (stillLiving D)) (some c) ≤ Real.exp (-9*(N : ℝ)/4000) := by
  have hA : ∀ d ∈ stillLiving D, Real.exp (-(N : ℝ)/20) ≤
      growthObservable D (membraneObservable N (-1/20)) 0 d := by
    intro d hd
    cases d with
    | none => simp [stillLiving] at hd
    | some d =>
      apply Real.exp_le_exp.mpr
      have hm : (d.val.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast (hD d.val d.property).le
      change -(N : ℝ)/20 ≤ (-1/20)*((d.val.2 : ℝ)-(N : ℝ))
      linarith only [hm]
  have h := killed_late_clock γ a hγ ha N D hD hrate q t hq hclock hk
    (stillLiving D) (Real.exp (-(N : ℝ)/20)) hA c
  have hs : membraneObservable N (-1/20) c.val=1 := by simp [membraneObservable,hstart]
  rw [hs,mul_one] at h
  have hatime : -(19*a*(N : ℝ)/400)*(t : ℝ)-(-(N : ℝ)/20) = -9*(N : ℝ)/4000 := by
    calc
      _ = -(19*(N : ℝ)/400)*(a*(t : ℝ))+(N : ℝ)/20 := by ring
      _ = _ := by rw [ht]; ring
  simpa only [hatime] using exponential_probability_cancel _ _ _ h

end HeritableCompositions

import proofs.HeritableCompositions.StoppedGrowth
import proofs.HeritableCompositions.EventExponential

namespace HeritableCompositions
open FiniteCopy

noncomputable def membraneObservable (N : ℕ) (θ : ℝ) (c : Compartment) : ℝ :=
  Real.exp (θ*((c.2 : ℝ)-(N : ℝ)))

theorem membrane_observable_generator (γ θ : ℝ) (N : ℕ) (c : Compartment) :
    compartmentGenerator γ (membraneObservable N θ) c =
      γ*(c.1 2 : ℝ)*membraneObservable N θ c*(Real.exp θ-1) := by
  have he : Real.exp (θ*((c.2 : ℝ)+1-(N : ℝ))) =
      Real.exp (θ*((c.2 : ℝ)-(N : ℝ)))*Real.exp θ := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [compartmentGenerator,Fintype.sum_sum_type,nextCompartment,
    propensity,membraneObservable,Nat.cast_add,Nat.cast_one]
  simp only [sub_self,mul_zero,Finset.sum_const_zero,Fintype.sum_unique,zero_add]
  rw [he]
  ring

theorem early_clock_increment : Real.exp (1/5 : ℝ)-1 ≤ 6/25 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (by norm_num : |(1/5 : ℝ)| ≤ 1))).2
  linarith only [h]

theorem late_clock_increment : Real.exp (-1/20 : ℝ)-1 ≤ -19/400 := by
  have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (by norm_num : |(-1/20 : ℝ)| ≤ 1))).2
  linarith only [h]

theorem early_membrane_generator (γ b : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (c : Compartment)
    (hrate : γ*(c.1 2 : ℝ) ≤ 2*b*(N : ℝ)) :
    compartmentGenerator γ (membraneObservable N (1/5)) c ≤
      (12*b*(N : ℝ)/25)*membraneObservable N (1/5) c := by
  rw [membrane_observable_generator]
  have hW : 0 ≤ membraneObservable N (1/5) c := (Real.exp_pos _).le
  have hr0 : 0 ≤ γ*(c.1 2 : ℝ) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left early_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ membraneObservable N (1/5) c*(6/25))
  nlinarith only [hfirst,hsecond]

theorem late_membrane_generator (γ a : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (c : Compartment)
    (hrate : a*(N : ℝ) ≤ γ*(c.1 2 : ℝ)) :
    compartmentGenerator γ (membraneObservable N (-1/20)) c ≤
      -(19*a*(N : ℝ)/400)*membraneObservable N (-1/20) c := by
  rw [membrane_observable_generator]
  have hW : 0 ≤ membraneObservable N (-1/20) c := (Real.exp_pos _).le
  have hr0 : 0 ≤ γ*(c.1 2 : ℝ) := by positivity
  have hfirst := mul_le_mul_of_nonneg_left late_clock_increment (mul_nonneg hr0 hW)
  have hsecond := mul_le_mul_of_nonneg_right hrate (by positivity : 0 ≤ membraneObservable N (-1/20) c*(19/400))
  nlinarith only [hfirst,hsecond]

end HeritableCompositions

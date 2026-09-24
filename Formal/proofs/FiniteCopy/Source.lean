import Mathlib

/-! Literal directed source kernel. Real-polynomial rates are interpreted as
reaction propensities only on the count lattice; no CTMC theorem is assumed. -/
namespace FiniteCopy
abbrev Point := Fin 4 → ℝ
abbrev Counts := Fin 4 → ℕ

def jump : Fin 13 → Point :=
  ![![-1,1,1,0], ![1,-1,-1,0], ![0,0,-1,1], ![0,0,1,-1],
    ![0,0,2,-1], ![0,0,-2,1], ![1,0,0,0], ![-1,0,0,0],
    ![0,1,0,0], ![0,-1,0,0], ![2,-1,0,0], ![-2,1,0,0], ![0,0,0,-1]]

noncomputable def densityRates (e q : ℝ) (x : Point) : Fin 13 → ℝ :=
  ![x 0, x 1*x 2, 16*x 2, x 3, x 3, 2*x 2*(x 2-q),
    6, x 0, 27, x 1, e*x 1, e*x 0*(x 0-q), x 3/10000]

noncomputable def concentration (N : ℕ) (n : Counts) : Point :=
  fun i => (n i : ℝ)/(N : ℝ)

theorem lattice_pair_nonneg (N n : ℕ) :
    0 ≤ ((n : ℝ)/N)*((n : ℝ)/N-1/(N : ℝ)) := by
  rcases n with _ | n
  · simp
  · have hn : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_nonneg (div_nonneg (by positivity) hN)
      (sub_nonneg.mpr (div_le_div_of_nonneg_right hn hN))

theorem lattice_rates_nonneg (e : ℝ) (he : 0 ≤ e) (N : ℕ) (n : Counts)
    (r : Fin 13) : 0 ≤ densityRates e (1/(N : ℝ)) (concentration N n) r := by
  have hp (i : Fin 4) : 0 ≤ concentration N n i := by
    dsimp [concentration]; positivity
  have hpair (i : Fin 4) := lattice_pair_nonneg N (n i)
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  fin_cases r <;> norm_num [densityRates]
  all_goals try positivity
  · simpa [concentration, mul_assoc] using mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hpair 2)
  · simpa [concentration, mul_assoc] using mul_nonneg he (hpair 0)

noncomputable def drift (e q : ℝ) (x : Point) : Point :=
  fun i => ∑ r : Fin 13, densityRates e q x r * jump r i

theorem drift_formula (e q : ℝ) (x : Point) :
    drift e q x =
    ![6-2*x 0+x 1*x 2+2*e*(x 1-(x 0)^2)+2*e*q*x 0,
      27+x 0-(1+x 2)*x 1-e*(x 1-(x 0)^2)-e*q*x 0,
      x 0-x 1*x 2-16*x 2-4*(x 2)^2+3*x 3+4*q*x 2,
      16*x 2+2*(x 2)^2-(2+1/10000)*x 3-2*q*x 2] := by
  ext i
  fin_cases i <;> norm_num [drift, densityRates, jump, Fin.sum_univ_succ] <;> ring

theorem finite_volume_correction (e q : ℝ) (x : Point) :
    drift e q x - drift e 0 x = ![2*e*q*x 0,-e*q*x 0,4*q*x 2,-2*q*x 2] := by
  rw [drift_formula, drift_formula]
  ext i
  fin_cases i <;> norm_num

noncomputable def weight (e : ℝ) : Point := ![e+3/2,2*e+1,1,3/2]
noncomputable def mass (e : ℝ) (x : Point) : ℝ := ∑ i, weight e i*x i
noncomputable def massDrift (e q : ℝ) (x : Point) : ℝ :=
  ∑ i, weight e i*drift e q x i

theorem mass_drift_formula (e q : ℝ) (x : Point) :
    massDrift e q x = 36+60*e-x 0-x 1-(e+1/2)*x 1*x 2+
      8*x 2-(x 2)^2+q*x 2-2*e*x 0*(x 0-q)-3*x 3/20000 := by
  unfold massDrift
  rw [drift_formula]
  norm_num [weight, Fin.sum_univ_succ]
  ring

theorem foster_remainder (e q : ℝ) (x : Point) :
    61+60*e-mass e x/10000-massDrift e q x =
    (1-(e+3/2)/10000)*x 0+(1-(2*e+1)/10000)*x 1+
      (e+1/2)*x 1*x 2+2*e*x 0*(x 0-q)+(x 2-5)^2+
      (2-1/10000-q)*x 2 := by
  rw [mass_drift_formula]
  norm_num [mass, weight, Fin.sum_univ_succ, show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring

theorem lattice_foster (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (N : ℕ) (hN : 1 ≤ N) (n : Counts) :
    massDrift e (1/(N : ℝ)) (concentration N n) ≤
      61+60*e-mass e (concentration N n)/10000 := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hq : 1/(N : ℝ) ≤ 1 := (div_le_one (by linarith)).2 hNr
  have hp (i : Fin 4) : 0 ≤ concentration N n i := by
    dsimp [concentration]; positivity
  have hpair := lattice_pair_nonneg N (n 0)
  have hA : 0 ≤ 1-(e+3/2)/10000 := by linarith
  have hB : 0 ≤ 1-(2*e+1)/10000 := by linarith
  have hz : 0 ≤ 2-1/10000-1/(N : ℝ) := by linarith
  have hp' : 0 ≤ 2*e*concentration N n 0*(concentration N n 0-1/(N : ℝ)) := by
    simpa [concentration, mul_assoc] using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he) hpair
  have hr := foster_remainder e (1/(N : ℝ)) (concentration N n)
  have hcross : 0 ≤ (e+1/2)*concentration N n 1*concentration N n 2 :=
    mul_nonneg (mul_nonneg (by linarith) (hp 1)) (hp 2)
  nlinarith [mul_nonneg hA (hp 0), mul_nonneg hB (hp 1),
    mul_nonneg hz (hp 2), sq_nonneg (concentration N n 2-5)]

end FiniteCopy

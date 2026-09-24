import proofs.FiniteCopy.LocalSourceBounds
import proofs.FiniteCopy.LocalExponentialRate
import proofs.FiniteCopy.ExponentialFoster

namespace FiniteCopy
open CoreCouplingCAC Set

noncomputable def lowExponential (N : ℕ) (s x : Point) : ℝ :=
  Real.exp ((N : ℝ)*localAlpha*lowEnergy (fun i => x i-s i))

theorem lowexponential_generator_identity (N : ℕ) (hN : 1 ≤ N) (s x : Point) :
    generator (1/100000) N (lowExponential N s) x =
      (N : ℝ)*lowExponential N s x*
        ∑ r, densityRates (1/100000) (1/(N : ℝ)) x r*
          (Real.exp (localAlpha*(2*lowPair (fun i => x i-s i) (jump r)+
            (1/(N : ℝ))*lowEnergy (jump r)))-1) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hstep (r : Fin 13) : lowExponential N s (fun i => x i+jump r i/(N : ℝ)) =
      lowExponential N s x*Real.exp (localAlpha*(2*lowPair (fun i => x i-s i) (jump r)+
        (1/(N : ℝ))*lowEnergy (jump r))) := by
    unfold lowExponential
    rw [← Real.exp_add]
    congr 1
    unfold lowEnergy lowPair
    field_simp
    ring
  unfold generator
  simp_rw [hstep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem lowlocal_generator (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) N (lowExponential N (pointOfState (lift sourceRates z))) (concentration N n) ≤
      localAlpha*lowExponential N (pointOfState (lift sourceRates z)) (concentration N n)*
        (-(N : ℝ)/2*normSq (fun i => concentration N n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let x := concentration N n
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N : ℝ)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNpos).mpr hNr
  have hb := low_source_box z hz
  have hsu (i : Fin 4) : s i ≤ 34 := by
    fin_cases i <;> norm_num [s,pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]
  have hx (i) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,concentration]; positivity
    · have hh := (abs_le.mp (hy i)).2
      change x i-s i ≤ 1/400 at hh
      linarith [hsu i]
  have hxa (i) : |x i| ≤ 35 := by rw [abs_of_nonneg (hx i).1]; exact (hx i).2
  have hd := low_source_dissipation z hz hs y hy
  have hxy : (fun i => s i+y i) = x := by funext i; dsimp [y]; ring
  change 2*lowPair y (drift (1/100000) 0 (fun i => s i+y i)) ≤ _ at hd
  rw [hxy] at hd
  have hc := mul_le_mul_of_nonneg_left (lowcorrection_bound y x hy hxa) hq
  have hfirst : (∑ r, densityRates (1/100000) q x r*(2*lowPair y (jump r))) ≤
      -(59/100)*normSq y+10000*q := by
    rw [lowpair_drift_sum,lowpair_correction_identity]
    nlinarith only [hd,hc]
  have hr := local_exponential_rate_bound (densityRates (1/100000) q x)
    (fun r => 2*lowPair y (jump r)) (fun r => lowEnergy (jump r)) q (normSq y)
    (lattice_rates_nonneg (1/100000) (by norm_num) N n)
    (local_rate_sum_upper x q hq hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (lowjump_pair_sq y) lowjump_energy_bound hfirst
  rw [lowexponential_generator_identity N hN]
  have hm := mul_le_mul_of_nonneg_left hr (by unfold lowExponential; positivity :
    0 ≤ (N : ℝ)*lowExponential N s x)
  have heq : (N : ℝ)*lowExponential N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*lowExponential N s x*(-(N : ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [heq] at hm
  exact hm

noncomputable def highExponential (N : ℕ) (s x : Point) : ℝ :=
  Real.exp ((N : ℝ)*localAlpha*highEnergy (fun i => x i-s i))

theorem highexponential_generator_identity (N : ℕ) (hN : 1 ≤ N) (s x : Point) :
    generator (1/100000) N (highExponential N s) x =
      (N : ℝ)*highExponential N s x*
        ∑ r, densityRates (1/100000) (1/(N : ℝ)) x r*
          (Real.exp (localAlpha*(2*highPair (fun i => x i-s i) (jump r)+
            (1/(N : ℝ))*highEnergy (jump r)))-1) := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hstep (r : Fin 13) : highExponential N s (fun i => x i+jump r i/(N : ℝ)) =
      highExponential N s x*Real.exp (localAlpha*(2*highPair (fun i => x i-s i) (jump r)+
        (1/(N : ℝ))*highEnergy (jump r))) := by
    unfold highExponential
    rw [← Real.exp_add]
    congr 1
    unfold highEnergy highPair
    field_simp
    ring
  unfold generator
  simp_rw [hstep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem highlocal_generator (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) N (highExponential N (pointOfState (lift sourceRates z))) (concentration N n) ≤
      localAlpha*highExponential N (pointOfState (lift sourceRates z)) (concentration N n)*
        (-(N : ℝ)/2*normSq (fun i => concentration N n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let x := concentration N n
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N : ℝ)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNpos).mpr hNr
  have hb := high_source_box z hz
  have hsu (i : Fin 4) : s i ≤ 34 := by
    fin_cases i <;> norm_num [s,pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]
  have hx (i) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,concentration]; positivity
    · have hh := (abs_le.mp (hy i)).2
      change x i-s i ≤ 1/400 at hh
      linarith [hsu i]
  have hxa (i) : |x i| ≤ 35 := by rw [abs_of_nonneg (hx i).1]; exact (hx i).2
  have hd := high_source_dissipation z hz hs y hy
  have hxy : (fun i => s i+y i) = x := by funext i; dsimp [y]; ring
  change 2*highPair y (drift (1/100000) 0 (fun i => s i+y i)) ≤ _ at hd
  rw [hxy] at hd
  have hc := mul_le_mul_of_nonneg_left (highcorrection_bound y x hy hxa) hq
  have hfirst : (∑ r, densityRates (1/100000) q x r*(2*highPair y (jump r))) ≤
      -(59/100)*normSq y+10000*q := by
    rw [highpair_drift_sum,highpair_correction_identity]
    nlinarith only [hd,hc]
  have hr := local_exponential_rate_bound (densityRates (1/100000) q x)
    (fun r => 2*highPair y (jump r)) (fun r => highEnergy (jump r)) q (normSq y)
    (lattice_rates_nonneg (1/100000) (by norm_num) N n)
    (local_rate_sum_upper x q hq hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (highjump_pair_sq y) highjump_energy_bound hfirst
  rw [highexponential_generator_identity N hN]
  have hm := mul_le_mul_of_nonneg_left hr (by unfold highExponential; positivity :
    0 ≤ (N : ℝ)*highExponential N s x)
  have heq : (N : ℝ)*highExponential N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*highExponential N s x*(-(N : ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [heq] at hm
  exact hm

end FiniteCopy

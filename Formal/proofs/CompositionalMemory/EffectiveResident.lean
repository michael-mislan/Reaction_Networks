import proofs.FiniteCopy.LocalGenerator
import proofs.CompositionalMemory.Scaling

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC Set

noncomputable def effectiveConcentration (v : ℝ) (n : Counts) : Point :=
  fun i => (n i : ℝ)/v

noncomputable def effectiveGenerator (e v : ℝ) (W : Point → ℝ) (x : Point) : ℝ :=
  v * ∑ r : Fin 13, densityRates e (1/v) x r *
    (W (fun i => x i+jump r i/v)-W x)

theorem effective_rates_nonneg (e : ℝ) (he : 0 ≤ e) (v : ℝ) (hv : 0 ≤ v)
    (n : Counts) (r : Fin 13) :
    0 ≤ densityRates e (1/v) (effectiveConcentration v n) r := by
  have hp (i : Fin 4) : 0 ≤ effectiveConcentration v n i := by
    dsimp [effectiveConcentration]; positivity
  have hpair (i : Fin 4) := real_volume_pair_nonneg v hv (n i)
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  fin_cases r <;> norm_num [densityRates]
  all_goals try positivity
  · simpa [effectiveConcentration, mul_assoc] using
      mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hpair 2)
  · simpa [effectiveConcentration, mul_assoc] using mul_nonneg he (hpair 0)

noncomputable def lowVolumeExponential (N : ℝ) (s x : Point) : ℝ :=
  Real.exp ((N : ℝ)*localAlpha*lowEnergy (fun i => x i-s i))

theorem low_volume_generator_identity (N : ℝ) (hN : 1 ≤ N) (s x : Point) :
    effectiveGenerator (1/100000) N (lowVolumeExponential N s) x =
      (N : ℝ)*lowVolumeExponential N s x*
        ∑ r, densityRates (1/100000) (1/(N : ℝ)) x r*
          (Real.exp (localAlpha*(2*lowPair (fun i => x i-s i) (jump r)+
            (1/(N : ℝ))*lowEnergy (jump r)))-1) := by
  have hNr : (N : ℝ) ≠ 0 := by linarith only [hN]
  have hstep (r : Fin 13) : lowVolumeExponential N s (fun i => x i+jump r i/(N : ℝ)) =
      lowVolumeExponential N s x*Real.exp (localAlpha*(2*lowPair (fun i => x i-s i) (jump r)+
        (1/(N : ℝ))*lowEnergy (jump r))) := by
    unfold lowVolumeExponential
    rw [← Real.exp_add]
    congr 1
    unfold lowEnergy lowPair
    field_simp
    ring
  unfold effectiveGenerator
  simp_rw [hstep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem low_real_volume_generator (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N : ℝ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |effectiveConcentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    effectiveGenerator (1/100000) N (lowVolumeExponential N (pointOfState (lift sourceRates z))) (effectiveConcentration N n) ≤
      localAlpha*lowVolumeExponential N (pointOfState (lift sourceRates z)) (effectiveConcentration N n)*
        (-(N : ℝ)/2*normSq (fun i => effectiveConcentration N n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let x := effectiveConcentration N n
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N : ℝ)
  have hNr : (1 : ℝ) ≤ N := hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNpos).mpr hNr
  have hb := low_source_box z hz
  have hsu (i : Fin 4) : s i ≤ 34 := by
    fin_cases i <;> norm_num [s,pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]
  have hx (i) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,effectiveConcentration]; positivity
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
    (effective_rates_nonneg (1/100000) (by norm_num) N hNpos.le n)
    (local_rate_sum_upper x q hq hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (lowjump_pair_sq y) lowjump_energy_bound hfirst
  rw [low_volume_generator_identity N hN]
  have hm := mul_le_mul_of_nonneg_left hr (by unfold lowVolumeExponential; positivity :
    0 ≤ (N : ℝ)*lowVolumeExponential N s x)
  have heq : (N : ℝ)*lowVolumeExponential N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*lowVolumeExponential N s x*(-(N : ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [heq] at hm
  exact hm

noncomputable def highVolumeExponential (N : ℝ) (s x : Point) : ℝ :=
  Real.exp ((N : ℝ)*localAlpha*highEnergy (fun i => x i-s i))

theorem high_volume_generator_identity (N : ℝ) (hN : 1 ≤ N) (s x : Point) :
    effectiveGenerator (1/100000) N (highVolumeExponential N s) x =
      (N : ℝ)*highVolumeExponential N s x*
        ∑ r, densityRates (1/100000) (1/(N : ℝ)) x r*
          (Real.exp (localAlpha*(2*highPair (fun i => x i-s i) (jump r)+
            (1/(N : ℝ))*highEnergy (jump r)))-1) := by
  have hNr : (N : ℝ) ≠ 0 := by linarith only [hN]
  have hstep (r : Fin 13) : highVolumeExponential N s (fun i => x i+jump r i/(N : ℝ)) =
      highVolumeExponential N s x*Real.exp (localAlpha*(2*highPair (fun i => x i-s i) (jump r)+
        (1/(N : ℝ))*highEnergy (jump r))) := by
    unfold highVolumeExponential
    rw [← Real.exp_add]
    congr 1
    unfold highEnergy highPair
    field_simp
    ring
  unfold effectiveGenerator
  simp_rw [hstep]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem high_real_volume_generator (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z))
    (N : ℝ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |effectiveConcentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    effectiveGenerator (1/100000) N (highVolumeExponential N (pointOfState (lift sourceRates z))) (effectiveConcentration N n) ≤
      localAlpha*highVolumeExponential N (pointOfState (lift sourceRates z)) (effectiveConcentration N n)*
        (-(N : ℝ)/2*normSq (fun i => effectiveConcentration N n i-pointOfState (lift sourceRates z) i)+100000000) := by
  let s := pointOfState (lift sourceRates z)
  let x := effectiveConcentration N n
  let y : Point := fun i => x i-s i
  let q : ℝ := 1/(N : ℝ)
  have hNr : (1 : ℝ) ≤ N := hN
  have hNpos : 0 < (N : ℝ) := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := (div_le_one hNpos).mpr hNr
  have hb := high_source_box z hz
  have hsu (i : Fin 4) : s i ≤ 34 := by
    fin_cases i <;> norm_num [s,pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]
  have hx (i) : 0 ≤ x i ∧ x i ≤ 35 := by
    constructor
    · dsimp [x,effectiveConcentration]; positivity
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
    (effective_rates_nonneg (1/100000) (by norm_num) N hNpos.le n)
    (local_rate_sum_upper x q hq hx) hq hq1 (normSq_nonneg y) (normSq_small y hy)
    (highjump_pair_sq y) highjump_energy_bound hfirst
  rw [high_volume_generator_identity N hN]
  have hm := mul_le_mul_of_nonneg_left hr (by unfold highVolumeExponential; positivity :
    0 ≤ (N : ℝ)*highVolumeExponential N s x)
  have heq : (N : ℝ)*highVolumeExponential N s x*(localAlpha*(-(1/2)*normSq y+100000000*q)) =
      localAlpha*highVolumeExponential N s x*(-(N : ℝ)/2*normSq y+100000000) := by
    dsimp [q]
    field_simp
  rw [heq] at hm
  exact hm

end CompositionalMemory

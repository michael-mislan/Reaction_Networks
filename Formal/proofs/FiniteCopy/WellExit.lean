import proofs.FiniteCopy.EnergyEnvelope
import proofs.FiniteCopy.WellDomains
import proofs.FiniteCopy.StoppedDecay

namespace FiniteCopy
open CoreCouplingCAC Set
open scoped NNReal

theorem lowroot_upper (z : ℝ) (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000)) (i : Fin 4) :
    pointOfState (lift sourceRates z) i ≤ 34 := by
  have hb := low_source_box z hz
  fin_cases i <;> norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]

noncomputable def lowWellDomain (z : ℝ) (N : ℕ) (b : ℝ) : Finset Counts :=
  energyDomain N (pointOfState (lift sourceRates z)) lowEnergy b

theorem lowlocal_generator_ceiling (z : ℝ) (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) N (lowExponential N (pointOfState (lift sourceRates z))) (concentration N n) ≤ localCeiling := by
  let y : Point := fun i => concentration N n i-pointOfState (lift sourceRates z) i
  have hE : lowEnergy y ≤ 42*normSq y := by
    have h := lowEnergy_upper y
    nlinarith only [h,normSq_nonneg y]
  exact (lowlocal_generator z hz hs N hN n hy).trans
    (energy_drift_envelope (N : ℝ) (normSq y) (lowEnergy y) (Nat.cast_nonneg N) (normSq_nonneg y) hE)

theorem lowwell_exit_bound (z : ℝ) (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (N : ℕ) (hN : 1 ≤ N)
    (b : ℝ) (hb : b ≤ 1/32000000) (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (stoppedCountModel (1/100000) (by norm_num) N (lowWellDomain z N b)).total s ≤ q)
    (n : {n : Counts // n ∈ lowWellDomain z N b}) :
    Real.exp ((N : ℝ)*localAlpha*b)*
      ((stoppedCountModel (1/100000) (by norm_num) N (lowWellDomain z N b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some n) ≤
      lowExponential N (pointOfState (lift sourceRates z)) (concentration N n.val)+(t : ℝ)*localCeiling := by
  classical
  let s := pointOfState (lift sourceRates z)
  have hmem (m : Counts) : m ∈ lowWellDomain z N b ↔ lowEnergy (fun i => concentration N m i-s i) < b :=
    mem_energyDomain N hN m s (lowroot_upper z hz) lowEnergy lowEnergy_lower b hb
  apply stopped_source_event_bound (1/100000) (by norm_num) N
    (lowWellDomain z N b) (lowExponential N s)
    (Real.exp ((N : ℝ)*localAlpha*b)) localCeiling (Real.exp_pos _).le localCeiling_nonneg
  · intro m _; exact (Real.exp_pos _).le
  · intro m _ r _ hout
    have hE : b ≤ lowEnergy (fun i => concentration N (nextCounts m r) i-s i) :=
      le_of_not_gt (fun h => hout ((hmem _).mpr h))
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hE (by unfold localAlpha; positivity)
  · intro m hm
    apply lowlocal_generator_ceiling z hz hs N hN m
    exact small_energy_coordinates lowEnergy lowEnergy_lower _ (((hmem m).mp hm).trans_le hb)

theorem highroot_upper (z : ℝ) (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) (i : Fin 4) :
    pointOfState (lift sourceRates z) i ≤ 34 := by
  have hb := high_source_box z hz
  fin_cases i <;> norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals linarith only [hb.1.2,hb.2.1.2,hb.2.2.2,hz.2]

noncomputable def highWellDomain (z : ℝ) (N : ℕ) (b : ℝ) : Finset Counts :=
  energyDomain N (pointOfState (lift sourceRates z)) highEnergy b

theorem highlocal_generator_ceiling (z : ℝ) (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (N : ℕ) (hN : 1 ≤ N) (n : Counts)
    (hy : ∀ i, |concentration N n i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    generator (1/100000) N (highExponential N (pointOfState (lift sourceRates z))) (concentration N n) ≤ localCeiling := by
  let y : Point := fun i => concentration N n i-pointOfState (lift sourceRates z) i
  have hE : highEnergy y ≤ 42*normSq y := by
    have h := highEnergy_upper y
    nlinarith only [h,normSq_nonneg y]
  exact (highlocal_generator z hz hs N hN n hy).trans
    (energy_drift_envelope (N : ℝ) (normSq y) (highEnergy y) (Nat.cast_nonneg N) (normSq_nonneg y) hE)

theorem highwell_exit_bound (z : ℝ) (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (hs : Stationary sourceRates (lift sourceRates z)) (N : ℕ) (hN : 1 ≤ N)
    (b : ℝ) (hb : b ≤ 1/32000000) (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (stoppedCountModel (1/100000) (by norm_num) N (highWellDomain z N b)).total s ≤ q)
    (n : {n : Counts // n ∈ highWellDomain z N b}) :
    Real.exp ((N : ℝ)*localAlpha*b)*
      ((stoppedCountModel (1/100000) (by norm_num) N (highWellDomain z N b)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator {none}) (some n) ≤
      highExponential N (pointOfState (lift sourceRates z)) (concentration N n.val)+(t : ℝ)*localCeiling := by
  classical
  let s := pointOfState (lift sourceRates z)
  have hmem (m : Counts) : m ∈ highWellDomain z N b ↔ highEnergy (fun i => concentration N m i-s i) < b :=
    mem_energyDomain N hN m s (highroot_upper z hz) highEnergy highEnergy_lower b hb
  apply stopped_source_event_bound (1/100000) (by norm_num) N
    (highWellDomain z N b) (highExponential N s)
    (Real.exp ((N : ℝ)*localAlpha*b)) localCeiling (Real.exp_pos _).le localCeiling_nonneg
  · intro m _; exact (Real.exp_pos _).le
  · intro m _ r _ hout
    have hE : b ≤ highEnergy (fun i => concentration N (nextCounts m r) i-s i) :=
      le_of_not_gt (fun h => hout ((hmem _).mpr h))
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hE (by unfold localAlpha; positivity)
  · intro m hm
    apply highlocal_generator_ceiling z hz hs N hN m
    exact small_energy_coordinates highEnergy highEnergy_lower _ (((hmem m).mp hm).trans_le hb)

end FiniteCopy

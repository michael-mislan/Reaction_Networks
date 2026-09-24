import proofs.FiniteCopy.InitialCertificates
import proofs.FiniteCopy.SourceBoxes

namespace FiniteCopy
open CoreCouplingCAC Set

theorem floor_concentration_bounds (N : ℕ) (hN : 1000000000000 ≤ N) (v : ℝ) (hv : 0 ≤ v) :
    v-1/1000000000000 ≤ (⌊(N : ℝ)*v⌋₊ : ℝ)/(N : ℝ) ∧
      (⌊(N : ℝ)*v⌋₊ : ℝ)/(N : ℝ) ≤ v := by
  have hNr : (1000000000000 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 < (N : ℝ) := by linarith only [hNr]
  have hlo := Nat.floor_le (mul_nonneg hp.le hv)
  have hhi := Nat.lt_floor_add_one ((N : ℝ)*v)
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith only [hhi,hNr]
  · exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hlo)

theorem rounded_initial_point (E : Point → ℝ)
    (hcert : ∀ y : Point,
      (6999/1000000000000 ≤ y 0 ∧ y 0 ≤ 7/1000000000) →
      |y 1| ≤ 1/1000000000000 → |y 2| ≤ 1/1000000000000 → |y 3| ≤ 1/1000000000000 →
      2/51200000000000000 ≤ E y ∧ E y ≤ 4/51200000000000000)
    (N : ℕ) (hN : 1000000000000 ≤ N) (s : Point) (hs : ∀ i, 0 ≤ s i) :
    ∃ n : Counts, 2/51200000000000000 ≤ E (fun i => concentration N n i-s i) ∧
      E (fun i => concentration N n i-s i) ≤ 4/51200000000000000 := by
  let n : Counts := ![⌊(N : ℝ)*(s 0+7/1000000000)⌋₊,⌊(N : ℝ)*s 1⌋₊,
    ⌊(N : ℝ)*s 2⌋₊,⌊(N : ℝ)*s 3⌋₊]
  have h0 := floor_concentration_bounds N hN (s 0+7/1000000000) (by linarith [hs 0])
  have h1 := floor_concentration_bounds N hN (s 1) (hs 1)
  have h2 := floor_concentration_bounds N hN (s 2) (hs 2)
  have h3 := floor_concentration_bounds N hN (s 3) (hs 3)
  refine ⟨n,hcert _ ?_ ?_ ?_ ?_⟩
  · change 6999/1000000000000 ≤ (⌊(N : ℝ)*(s 0+7/1000000000)⌋₊ : ℝ)/(N : ℝ)-s 0 ∧
      (⌊(N : ℝ)*(s 0+7/1000000000)⌋₊ : ℝ)/(N : ℝ)-s 0 ≤ 7/1000000000
    constructor <;> linarith only [h0.1,h0.2]
  · change |(⌊(N : ℝ)*s 1⌋₊ : ℝ)/(N : ℝ)-s 1| ≤ 1/1000000000000
    apply abs_le.mpr
    constructor <;> linarith only [h1.1,h1.2]
  · change |(⌊(N : ℝ)*s 2⌋₊ : ℝ)/(N : ℝ)-s 2| ≤ 1/1000000000000
    apply abs_le.mpr
    constructor <;> linarith only [h2.1,h2.2]
  · change |(⌊(N : ℝ)*s 3⌋₊ : ℝ)/(N : ℝ)-s 3| ≤ 1/1000000000000
    apply abs_le.mpr
    constructor <;> linarith only [h3.1,h3.2]

theorem low_initial_lattice_nonempty (z : ℝ)
    (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (N : ℕ) (hN : 1000000000000 ≤ N) :
    ∃ n : Counts, 2/51200000000000000 ≤ lowEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ∧
      lowEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ≤ 4/51200000000000000 := by
  apply rounded_initial_point lowEnergy lowinitial_energy N hN
  have hb := low_source_box z hz
  intro i
  fin_cases i <;> norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals linarith only [hb.1.1,hb.2.1.1,hb.2.2.1,hz.1]

theorem high_initial_lattice_nonempty (z : ℝ)
    (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (N : ℕ) (hN : 1000000000000 ≤ N) :
    ∃ n : Counts, 2/51200000000000000 ≤ highEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ∧
      highEnergy (fun i => concentration N n i-pointOfState (lift sourceRates z) i) ≤ 4/51200000000000000 := by
  apply rounded_initial_point highEnergy highinitial_energy N hN
  have hb := high_source_box z hz
  intro i
  fin_cases i <;> norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals linarith only [hb.1.1,hb.2.1.1,hb.2.2.1,hz.1]

end FiniteCopy

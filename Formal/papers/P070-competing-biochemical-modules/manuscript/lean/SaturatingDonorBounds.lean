import Mathlib

/-!
Source-band algebra for a saturating finite donor.

`sEff s0 K Q0 Q = s0 * (Q/(K+Q)) / (Q0/(K+Q0))` is the effective regeneration
scale of a donor with affinity scale `K`, normalised so that `sEff = s0` at the
initial stock `Q0`.  The lemmas give the exact source drop and the sufficient
stock condition used in the finite-mission corollary.  They are pure real
algebra; the coupled flow argument that uses them is conventional.
-/

namespace DynamicSharedResource.SaturatingDonor
noncomputable section

def sEff (s0 K Q0 Q : ℝ) : ℝ := s0 * (Q / (K + Q)) / (Q0 / (K + Q0))

theorem sEff_initial (s0 K Q0 : ℝ) (hK : 0 < K) (hQ0 : 0 < Q0) :
    sEff s0 K Q0 Q0 = s0 := by
  unfold sEff
  have h1 : K + Q0 ≠ 0 := by positivity
  field_simp

theorem source_drop_eq (s0 K Q0 Q : ℝ) (hK : 0 < K) (hQ0 : 0 < Q0) (hQ : 0 < Q) :
    s0 - sEff s0 K Q0 Q = s0 * K * (Q0 - Q) / (Q0 * (K + Q)) := by
  unfold sEff
  have h1 : K + Q0 ≠ 0 := by positivity
  have h2 : K + Q ≠ 0 := by positivity
  field_simp
  ring

theorem source_drop_nonneg (s0 K Q0 Q : ℝ) (hs : 0 ≤ s0) (hK : 0 < K) (hQ0 : 0 < Q0)
    (hQ : 0 < Q) (hle : Q ≤ Q0) : 0 ≤ s0 - sEff s0 K Q0 Q := by
  rw [source_drop_eq s0 K Q0 Q hK hQ0 hQ]
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg hs hK.le) (by linarith)
  · positivity

theorem source_drop_le (s0 K Q0 D Q : ℝ) (hs : 0 ≤ s0) (hK : 0 < K) (hD0 : 0 ≤ D)
    (hD : D < Q0) (hlo : Q0 - D ≤ Q) :
    s0 - sEff s0 K Q0 Q ≤ s0 * K * D / (Q0 * (K + Q0 - D)) := by
  have hQ0 : 0 < Q0 := by linarith
  have hQ : 0 < Q := by linarith
  rw [source_drop_eq s0 K Q0 Q hK hQ0 hQ]
  have hden1 : 0 < Q0 * (K + Q) := by positivity
  have hden2 : 0 < Q0 * (K + Q0 - D) := by
    apply mul_pos hQ0; linarith
  rw [div_le_div_iff₀ hden1 hden2]
  have hsK : 0 ≤ s0 * K := mul_nonneg hs hK.le
  have h1 : Q0 - Q ≤ D := by linarith
  have h2 : K + Q0 - D ≤ K + Q := by linarith
  have h3 : 0 ≤ K + Q0 - D := by linarith
  have key : (Q0 - Q) * (K + Q0 - D) ≤ D * (K + Q) := by
    rcases le_or_gt (Q0 - Q) 0 with hneg | hpos
    · have hA : (Q0 - Q) * (K + Q0 - D) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h3
      have hB : 0 ≤ D * (K + Q) := by positivity
      linarith
    · calc (Q0 - Q) * (K + Q0 - D) ≤ D * (K + Q0 - D) :=
            mul_le_mul_of_nonneg_right h1 h3
        _ ≤ D * (K + Q) := mul_le_mul_of_nonneg_left h2 hD0
  calc s0 * K * (Q0 - Q) * (Q0 * (K + Q0 - D))
      = (s0 * K * Q0) * ((Q0 - Q) * (K + Q0 - D)) := by ring
    _ ≤ (s0 * K * Q0) * (D * (K + Q)) :=
        mul_le_mul_of_nonneg_left key (mul_nonneg hsK hQ0.le)
    _ = s0 * K * D * (Q0 * (K + Q)) := by ring

/-- One-second mission: `D = 16 * (251/250)`, stock 200 µM, affinity scale 0.01 µM. -/
theorem example_stock_200 :
    (3/25 : ℝ) * (1/100) * (16 * (251/250)) / (200 * (1/100 + 200 - 16 * (251/250)))
      < 1/1000000 := by norm_num

/-- One-second mission: stock 1500 µM, affinity scale 1 µM. -/
theorem example_stock_1500 :
    (3/25 : ℝ) * 1 * (16 * (251/250)) / (1500 * (1 + 1500 - 16 * (251/250)))
      < 1/1000000 := by norm_num

/-- The band condition gives membership in the checked source band. -/
theorem sEff_in_band (s0 K Q0 D Q δ : ℝ) (hs : 0 ≤ s0) (hK : 0 < K) (hD0 : 0 ≤ D)
    (hD : D < Q0) (hlo : Q0 - D ≤ Q) (hhi : Q ≤ Q0)
    (hband : s0 * K * D / (Q0 * (K + Q0 - D)) ≤ δ) :
    |sEff s0 K Q0 Q - s0| ≤ δ := by
  have hQ0 : 0 < Q0 := by linarith
  have hQ : 0 < Q := by linarith
  have h1 := source_drop_nonneg s0 K Q0 Q hs hK hQ0 hQ hhi
  have h2 := source_drop_le s0 K Q0 D Q hs hK hD0 hD hlo
  rw [abs_sub_comm, abs_of_nonneg h1]
  linarith

end
end DynamicSharedResource.SaturatingDonor

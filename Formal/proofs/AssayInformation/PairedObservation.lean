import proofs.AssayInformation.Identification
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace AssayInformation
open MeasureTheory Set

/-- Independent unit-exponential noise, with observed D_j>D_i.
The inner half-line is exactly E_j>(q_j/q_i)E_i. -/
def pairedExceedance (qi qj : ℝ) : ℝ :=
  ∫ u in Ioi 0, Real.exp (-u) * (∫ v in Ioi ((qj/qi)*u), Real.exp (-v))

theorem paired_exceedance_formula (qi qj : ℝ) (hi : 0 < qi) (hj : 0 < qj) :
    pairedExceedance qi qj = qi/(qi+qj) := by
  unfold pairedExceedance
  simp_rw [integral_exp_neg_Ioi,← Real.exp_add]
  have he : (fun u : ℝ => Real.exp (-u+ -((qj/qi)*u))) =
      (fun u => Real.exp ((-(1+qj/qi))*u)) := by
    funext u
    congr 1
    ring
  have hsum : 0 < 1+qj/qi := by positivity
  rw [he,integral_exp_mul_Ioi (by linarith : -(1+qj/qi) < 0)]
  norm_num
  have hs : qi+qj ≠ 0 := ne_of_gt (add_pos hi hj)
  have hn : -qj + -qi ≠ 0 := by linarith
  field_simp
  ring

theorem dwell_order_clock_cancel (ei ej qi qj c : ℝ)
    (hi : 0 < qi) (hj : 0 < qj) (hc : 0 < c) :
    ei/(c*qi) < ej/(c*qj) ↔ (qj/qi)*ei < ej := by
  rw [div_lt_div_iff₀ (mul_pos hc hi) (mul_pos hc hj)]
  constructor
  · intro h
    have h' : ei*qj < ej*qi := by nlinarith
    apply (mul_lt_mul_iff_right₀ hi).mp
    have he : (qj/qi)*ei*qi = ei*qj := by field_simp
    nlinarith [he]
  · intro h
    have h' : (qj/qi)*ei*qi < ej*qi := mul_lt_mul_of_pos_right h hi
    have he : (qj/qi)*ei*qi = ei*qj := by field_simp
    rw [he] at h'
    nlinarith

theorem source_shape_ratio (a R i j : ℝ) (ha : 0 < a)
    (hi0 : 0 ≤ i) (hij : i < j) (hjR : j < R) :
    (sourceRate a 1 R j / sourceRate a 1 R i) * ((a+i)/(a+j)) =
      capacityRatio R i j := by
  have hR : R ≠ 0 := ne_of_gt (lt_trans (lt_of_le_of_lt hi0 hij) hjR)
  have hai : a+i ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ha hi0)
  have haj : a+j ≠ 0 := by nlinarith
  have hRi : R-i ≠ 0 := by nlinarith
  unfold sourceRate capacityRatio
  field_simp

theorem reconstruct_from_paired_probability (a R i j : ℝ)
    (ha : 0 < a) (hi0 : 0 ≤ i) (hij : i < j) (hjR : j < R) :
    reconstruct
      (((1-pairedExceedance (sourceRate a 1 R i) (sourceRate a 1 R j)) /
        pairedExceedance (sourceRate a 1 R i) (sourceRate a 1 R j))*((a+i)/(a+j))) i j = R := by
  have hR : 0 < R := lt_trans (lt_of_le_of_lt hi0 hij) hjR
  have hqi : 0 < sourceRate a 1 R i := by
    unfold sourceRate
    have h : i/R < 1 := (div_lt_one hR).mpr (hij.trans hjR)
    positivity
  have hqj : 0 < sourceRate a 1 R j := by
    unfold sourceRate
    have hj0 : 0 ≤ j := hi0.trans hij.le
    have h : j/R < 1 := (div_lt_one hR).mpr hjR
    positivity
  rw [paired_exceedance_formula _ _ hqi hqj]
  have he : (1-sourceRate a 1 R i/(sourceRate a 1 R i+sourceRate a 1 R j)) /
      (sourceRate a 1 R i/(sourceRate a 1 R i+sourceRate a 1 R j)) =
      sourceRate a 1 R j/sourceRate a 1 R i := by
    have hs := ne_of_gt (add_pos hqi hqj)
    have hn := ne_of_gt hqi
    field_simp
    ring
  rw [he,source_shape_ratio a R i j ha hi0 hij hjR]
  exact capacity_reconstruction R i j (hij.trans hjR) hij

end AssayInformation

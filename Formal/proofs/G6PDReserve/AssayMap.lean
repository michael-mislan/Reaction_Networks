import Mathlib.Tactic

/-! Exact one-substrate observation ambiguity. This is not a complete G6PD law
and supplies no erythrocyte parameter values. -/
namespace G6PDReserve
noncomputable section

def assayRate (V K S : ℝ) : ℝ := V * S / (K + S)

theorem assay_calibration (A K S : ℝ) (hS : S ≠ 0) (hKS : K + S ≠ 0) :
    assayRate (A * (K + S) / S) K S = A := by
  unfold assayRate
  field_simp

theorem off_assay_formula (A K Sa Sp : ℝ) :
    assayRate (A * (K + Sa) / Sa) K Sp =
      A * Sp * (K + Sa) / (Sa * (K + Sp)) := by
  unfold assayRate
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem identical_assay_distinct_supply :
    assayRate (101/100) (1/10) 10 = 1 ∧
    assayRate (11/10) 1 10 = 1 ∧
    assayRate (101/100) (1/10) (1/10) = 101/200 ∧
    assayRate (11/10) 1 (1/10) = 1/10 ∧
    assayRate (11/10) 1 (1/10) < assayRate (101/100) (1/10) (1/10) := by
  norm_num [assayRate]

/-- Two positive-substrate observations at distinct substrates identify both
parameters of a positive one-substrate Michaelis-Menten law. -/
theorem two_assays_identify (V W K L S T : ℝ)
    (hV : 0 < V) (hK : 0 < K) (hL : 0 < L)
    (hS : 0 < S) (hT : 0 < T) (hST : S ≠ T)
    (heS : assayRate V K S = assayRate W L S)
    (heT : assayRate V K T = assayRate W L T) : V = W ∧ K = L := by
  have hs := (div_eq_div_iff (ne_of_gt (add_pos hK hS))
    (ne_of_gt (add_pos hL hS))).mp heS
  have ht := (div_eq_div_iff (ne_of_gt (add_pos hK hT))
    (ne_of_gt (add_pos hL hT))).mp heT
  have hs' : V * (L + S) = W * (K + S) := by nlinarith
  have ht' : V * (L + T) = W * (K + T) := by nlinarith
  have hp : (V - W) * (S - T) = 0 := by nlinarith [hs', ht']
  have hvw : V = W := by
    have := (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hST)
    linarith
  constructor
  · exact hvw
  · rw [← hvw] at hs'
    nlinarith

end
end G6PDReserve

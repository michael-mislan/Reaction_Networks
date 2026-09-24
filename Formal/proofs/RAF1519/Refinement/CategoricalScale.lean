import proofs.RAF1519.Refinement.CategoricalMGF

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem categorical_material_tail (c : ι → Fin 3 → ℝ)
    (hc : ∀ m a, 0 ≤ c m a) (htotal : ∀ m, ∑ a, c m a=1)
    (w : ι → ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (V sign : ℝ) (hV : 0 ≤ V) (hsign : |sign|=1) (hbound : (∑ m, w m) ≤ (161/160)*V) :
    categoricalTail c w sign (V/100) ≤ Real.exp (-V/100000) := by
  have h := categorical_deviation_tail c hc htotal w hw hw' sign (1/500) (V/100)
    hsign (by norm_num) (by norm_num)
  apply h.trans
  apply Real.exp_le_exp.mpr
  linarith

theorem categorical_stock_tail (c : ι → Fin 3 → ℝ)
    (hc : ∀ m a, 0 ≤ c m a) (htotal : ∀ m, ∑ a, c m a=1)
    (w : ι → ℝ) (hw : ∀ m, 0 ≤ w m) (hw' : ∀ m, w m ≤ 2)
    (V : ℝ) (hV : 0 ≤ V) (hbound : (∑ m, w m) ≤ (161/160)*V) :
    categoricalTail c w (-1) (V/4000) ≤ Real.exp (-V/100000000) := by
  have h := categorical_deviation_tail c hc htotal w hw hw' (-1) (1/10000) (V/4000)
    (by norm_num) (by norm_num) (by norm_num)
  apply h.trans
  apply Real.exp_le_exp.mpr
  linarith

end
end RAF1519.Refinement

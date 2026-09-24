import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace ACRZeroDivisors
open scoped BigOperators

theorem release_prefix (E : ℕ → ℝ) (n : ℕ) :
    E 0 + ∑ j ∈ Finset.range n, (E (j+1)-E j) = E n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; linarith

theorem release_residual_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q f ft : ι → ℝ) (w : ι → κ → ℝ) (E : κ → ℝ)
    (hf : ∀ i, f i=ft i+∑ j, w i j*E j) :
    ∑ i, q i*f i = (∑ i, q i*ft i)+∑ j, (∑ i, q i*w i j)*E j := by
  simp_rw [hf, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul, mul_assoc]

theorem release_storage {ι : Type*} [Fintype ι]
    (F : ℝ) (omega rates z : ι → ℝ) (hz : ∀ j, z j=F/rates j) :
    ∑ j, omega j*z j = F*∑ j, omega j/rates j := by
  simp_rw [hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem release_storage_capacity (F cost budget : ℝ) (hc : 0 < cost)
    (hs : F*cost ≤ budget) : F ≤ budget/cost := (le_div_iff₀ hc).2 hs

theorem product_loss_bound (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, a j ≤ 1) :
    1-(∏ j ∈ Finset.range n, a j) ≤ ∑ j ∈ Finset.range n, (1-a j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hp : 0 ≤ ∏ j ∈ Finset.range n, a j := Finset.prod_nonneg fun j _ => ha j
    have hp1 : (∏ j ∈ Finset.range n, a j) ≤ 1 := Finset.prod_le_one (fun j _ => ha j) (fun j _ => hb j)
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr (hb n))]

theorem leakage_stage (F prev rate loss z : ℝ) (hh : rate+loss ≠ 0)
    (hz : (rate+loss)*z=F*prev) : rate*z=F*(prev*(rate/(rate+loss))) := by
  have he : z=F*prev/(rate+loss) := (eq_div_iff hh).2 (by nlinarith [hz])
  rw [he]
  ring

theorem leakage_defect {ι : Type*} [Fintype ι]
    (F : ℝ) (w pi : ι → ℝ) :
    (∑ j, w j*(F*pi j))-(∑ j, w j*F) = -F*∑ j, w j*(1-pi j) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem leakage_fraction_bound (rate loss : ℝ) (hr : 0 < rate) (hl : 0 ≤ loss) :
    0 ≤ rate/(rate+loss) ∧ rate/(rate+loss) ≤ 1 ∧
    1-rate/(rate+loss)=loss/(rate+loss) ∧ loss/(rate+loss) ≤ loss/rate := by
  have hs : 0 < rate+loss := by positivity
  refine ⟨by positivity, (div_le_one hs).2 (by linarith), ?_, ?_⟩
  · field_simp
    ring
  · exact div_le_div_of_nonneg_left hl hr (by linarith)

end ACRZeroDivisors

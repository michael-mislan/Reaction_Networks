import proofs.RandomViability.BindingEntryExponential
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory RandomViability.Binding
open scoped BigOperators ENNReal
set_option maxHeartbeats 30000

variable {ι : Type*} [Fintype ι]

/-- Category0 retained, category1 withdrawn, category2 additional loss. -/
def categoricalMass (c : ι → Fin 3 → ℝ) (o : ι → Fin 3) : ℝ := ∏ m, c m (o m)
def categoricalStock (w : ι → ℝ) (o : ι → Fin 3) : ℝ := ∑ m, if o m=0 then w m else 0
def categoricalMean (c : ι → Fin 3 → ℝ) (w : ι → ℝ) : ℝ := ∑ m, c m 0*w m

theorem categoricalMass_nonneg (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a) (o : ι → Fin 3) :
    0 ≤ categoricalMass c o := Finset.prod_nonneg (fun m _ => hc m (o m))

theorem categoricalMass_total (c : ι → Fin 3 → ℝ) (hc : ∀ m, ∑ a, c m a=1) :
    ∑ o, categoricalMass c o=1 := by
  unfold categoricalMass
  rw [← Fintype.prod_sum]
  simp only [hc,Finset.prod_const_one]

def categoricalPMF (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a)
    (ht : ∀ m, ∑ a, c m a=1) : PMF (ι → Fin 3) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (categoricalMass c o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => categoricalMass_nonneg c hc o),
      categoricalMass_total c ht,ENNReal.ofReal_one])

theorem categorical_transform (c : ι → Fin 3 → ℝ) (hc : ∀ m, ∑ a, c m a=1)
    (w : ι → ℝ) (t : ℝ) :
    (∑ o, categoricalMass c o*Real.exp (t*categoricalStock w o)) =
      ∏ m, (1-c m 0+c m 0*Real.exp (t*w m)) := by
  have hid (o : ι → Fin 3) : categoricalMass c o*Real.exp (t*categoricalStock w o) =
      ∏ m, c m (o m)*Real.exp (t*(if o m=0 then w m else 0)) := by
    unfold categoricalMass categoricalStock
    rw [Finset.mul_sum,Real.exp_sum,Finset.prod_mul_distrib]
  simp_rw [hid]
  rw [← Fintype.prod_sum (fun (m : ι) (a : Fin 3) => c m a*Real.exp (t*(if a=0 then w m else 0)))]
  apply Finset.prod_congr rfl
  intro m _
  have hm := hc m
  norm_num [Fin.sum_univ_succ] at hm ⊢
  linarith

theorem categorical_retention_factor (p w t : ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hw' : w ≤ 2) (ht : |t| ≤ 1/100) :
    1-p+p*Real.exp (t*w) ≤ Real.exp (t*p*w+(6/5)*t^2*p*w) := by
  have hab : |t*w| ≤ 9/50 := by
    rw [abs_mul,abs_of_nonneg hw]
    exact (mul_le_mul ht hw' hw (by norm_num)).trans (by norm_num)
  have he := mul_le_mul_of_nonneg_left (exp_small_quadratic (t*w) hab) hp
  have hw2 : w^2 ≤ 2*w := by nlinarith
  have hq := mul_le_mul_of_nonneg_left hw2 (show 0 ≤ (3/5)*p*t^2 by positivity)
  have hh : 1-p+p*Real.exp (t*w) ≤ (t*p*w+(6/5)*t^2*p*w)+1 := by nlinarith
  exact hh.trans (Real.add_one_le_exp _)

end
end RAF1519.Refinement

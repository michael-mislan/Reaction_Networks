import proofs.RandomViability.ProductiveOperationProbability

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

/-- Uniform sampling of this finite product gives the prescribed independent
pair marks S,B and incidence marks H. Each pair's S is shared by both directions. -/
abbrev KineticMarkConfig (n : ℕ) :=
  (Reaction n → Fin 3) × (Reaction n → Fin 3) × (Reaction n → Molecule n → Fin 3)

def kineticMultiplier (i : Fin 3) : NNReal := 1+(i.val : NNReal)/2

theorem kinetic_multiplier_bounds (i : Fin 3) :
    (1 : ℝ) ≤ kineticMultiplier i ∧ (kineticMultiplier i : ℝ) ≤ 2 := by
  have hi : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 by omega)
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  norm_num [kineticMultiplier]
  constructor <;> linarith

def kineticBasal {n : ℕ} (u : KineticMarkConfig n) (r : Reaction n) : NNReal :=
  ⟨productiveEpsilon,by norm_num [productiveEpsilon]⟩ * kineticMultiplier (u.1 r) *
    kineticMultiplier (u.2.1 r)

def kineticCatalytic {n : ℕ} (u : KineticMarkConfig n) (r : Reaction n)
    (x : Molecule n) : NNReal :=
  4 * kineticMultiplier (u.1 r) * kineticMultiplier (u.2.2 r x)

theorem kinetic_basal_bounds {n : ℕ} (u : KineticMarkConfig n) (r : Reaction n) :
    productiveEpsilon ≤ (kineticBasal u r : ℝ) ∧
    (kineticBasal u r : ℝ) ≤ 4*productiveEpsilon := by
  have hs := kinetic_multiplier_bounds (u.1 r)
  have hb := kinetic_multiplier_bounds (u.2.1 r)
  have hp : 1 ≤ (kineticMultiplier (u.1 r) : ℝ)*kineticMultiplier (u.2.1 r) ∧
      (kineticMultiplier (u.1 r) : ℝ)*kineticMultiplier (u.2.1 r) ≤ 4 := by
    constructor
    · simpa using mul_le_mul hs.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ kineticMultiplier (u.1 r))
    · have hh := mul_le_mul hs.2 hb.2 (by linarith : (0 : ℝ) ≤ kineticMultiplier (u.2.1 r)) (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hh
      exact hh
  change productiveEpsilon ≤ productiveEpsilon*(kineticMultiplier (u.1 r) : ℝ)*
    kineticMultiplier (u.2.1 r) ∧ productiveEpsilon*(kineticMultiplier (u.1 r) : ℝ)*
    kineticMultiplier (u.2.1 r) ≤ 4*productiveEpsilon
  have he : 0 < productiveEpsilon := by norm_num [productiveEpsilon]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp.1 he.le]
  · nlinarith [mul_le_mul_of_nonneg_left hp.2 he.le]

theorem kinetic_catalytic_bounds {n : ℕ} (u : KineticMarkConfig n)
    (r : Reaction n) (x : Molecule n) :
    4 ≤ (kineticCatalytic u r x : ℝ) ∧ (kineticCatalytic u r x : ℝ) ≤ 16 := by
  have hs := kinetic_multiplier_bounds (u.1 r)
  have hh := kinetic_multiplier_bounds (u.2.2 r x)
  have hlo := mul_le_mul hs.1 hh.1 (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : (0 : ℝ) ≤ kineticMultiplier (u.1 r))
  have hhi := mul_le_mul hs.2 hh.2
    (by linarith : (0 : ℝ) ≤ kineticMultiplier (u.2.2 r x)) (by norm_num : (0 : ℝ) ≤ 2)
  norm_num only [kineticCatalytic,NNReal.coe_mul,NNReal.coe_ofNat]
  constructor <;> nlinarith

def uniformFiniteAverage {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i)/(Fintype.card ι : ℝ)

theorem uniform_finite_average_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (L U : ℝ) (h : ∀ i, L ≤ f i ∧ f i ≤ U) :
    L ≤ uniformFiniteAverage f ∧ uniformFiniteAverage f ≤ U := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold uniformFiniteAverage
  constructor
  · rw [le_div_iff₀ hc]
    calc
      _ = ∑ _i : ι, L := by simp [mul_comm]
      _ ≤ ∑ i : ι, f i := Finset.sum_le_sum (fun i _ => (h i).1)
  · rw [div_le_iff₀ hc]
    calc
      _ ≤ ∑ _i : ι, U := Finset.sum_le_sum (fun i _ => (h i).2)
      _ = _ := by simp [mul_comm]

end
end RandomViability

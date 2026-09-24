import proofs.G6PDReserve.SourceRate

namespace G6PDReserve
noncomputable section
open scoped BigOperators

abbrev Six := Fin 6 → ℝ
def PositiveSix (x : Six) : Prop := ∀ i, 0 < x i

/-- Parameter order: V, Kg, Kn, Kh, Ka, Kb. -/
def coefficients (p : Six) : Six :=
  ![1/p 0, p 1/p 0, p 2*p 1/p 0,
    p 2*p 1/(p 0*p 3), p 2*p 1/(p 0*p 4), p 2*p 1/(p 0*p 5)]
def parameters (b : Six) : Six :=
  ![1/b 0, b 1/b 0, b 2/b 1, b 2/b 3, b 2/b 4, b 2/b 5]

theorem parameters_positive (b : Six) (hb : PositiveSix b) :
    PositiveSix (parameters b) := by
  have h0 := hb 0; have h1 := hb 1; have h2 := hb 2
  have h3 := hb 3; have h4 := hb 4; have h5 := hb 5
  intro i
  fin_cases i <;> simp [parameters] <;> positivity

theorem coefficients_positive (p : Six) (hp : PositiveSix p) :
    PositiveSix (coefficients p) := by
  have h0 := hp 0; have h1 := hp 1; have h2 := hp 2
  have h3 := hp 3; have h4 := hp 4; have h5 := hp 5
  intro i
  fin_cases i <;> simp [coefficients] <;> positivity

theorem coefficients_parameters (b : Six) (hb : PositiveSix b) :
    coefficients (parameters b) = b := by
  have hn : ∀ i, b i ≠ 0 := fun i => ne_of_gt (hb i)
  funext i
  fin_cases i <;> simp [coefficients, parameters] <;> field_simp [hn 0, hn 1, hn 2, hn 3, hn 4, hn 5]

theorem parameters_coefficients (p : Six) (hp : PositiveSix p) :
    parameters (coefficients p) = p := by
  have hn : ∀ i, p i ≠ 0 := fun i => ne_of_gt (hp i)
  funext i
  fin_cases i <;> simp [coefficients, parameters] <;> field_simp [hn 0, hn 1, hn 2, hn 3, hn 4, hn 5]

def feature (N S H A B : ℝ) : Six :=
  ![1, 1/S, 1/(N*S), H/(N*S), A/(N*S), B/(N*S)]
def dot (x y : Six) : ℝ := ∑ i, x i * y i

def ObservationFeasible {ι : Type*} (F : ι → Six) (lo hi : ι → ℝ)
    (b : Six) : Prop := PositiveSix b ∧ ∀ i, 1/hi i ≤ dot (F i) b ∧ dot (F i) b ≤ 1/lo i

/-- A finite nonnegative dual certificate; no floating-point optimizer is trusted. -/
theorem finite_upper_certificate {ι : Type*} [Fintype ι]
    (A : ι → Six) (rhs y : ι → ℝ) (c b : Six)
    (hy : ∀ i, 0 ≤ y i) (hA : ∀ i, dot (A i) b ≤ rhs i)
    (hc : ∀ j, c j = ∑ i, y i * A i j) :
    dot c b ≤ ∑ i, y i * rhs i := by
  have he : dot c b = ∑ i, y i * dot (A i) b := by
    simp only [dot, hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hA i) (hy i)

theorem reciprocal_bounds (D L U : ℝ) (hL : 0 < L) (hLD : L ≤ D) (hDU : D ≤ U) :
    1/U ≤ 1/D ∧ 1/D ≤ 1/L := by
  have hD : 0 < D := lt_of_lt_of_le hL hLD
  constructor
  · exact one_div_le_one_div_of_le hD hDU
  · exact one_div_le_one_div_of_le hL hLD

end
end G6PDReserve

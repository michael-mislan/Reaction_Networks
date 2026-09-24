import Mathlib

namespace OptimalAffinityCorrected

noncomputable section

/-!
A source-realized counterexample to the proposed zero-diagonal correction.

  R1: X  <-> Y             rates 6,5
  R2: 2Y <-> 2X + 2Z      rates 5,4
  R3: 2Z <-> Y             rates 6,5

The response matrix is
`[[0,2,0],[1/2,0,1/2],[0,1,0]]`: every diagonal entry is zero, but reactions
2 and 3 form a directed recycling circuit.
-/

def circuitJ1 (x y : ℝ) : ℝ := 6 * x - 5 * y
def circuitJ2 (x y z : ℝ) : ℝ := 5 * y ^ 2 - 4 * x ^ 2 * z ^ 2
def circuitJ3 (y z : ℝ) : ℝ := 6 * z ^ 2 - 5 * y

def CircuitSteady (x y z : ℝ) : Prop :=
  circuitJ1 x y = circuitJ2 x y z ∧ circuitJ2 x y z = circuitJ3 y z

def circuitExpAffinity (x y z : ℝ) : ℝ :=
  ((6 * x) / (5 * y)) * ((5 * y ^ 2) / (4 * x ^ 2 * z ^ 2)) *
    ((6 * z ^ 2) / (5 * y))

def grossStoichiometricRatio (reactant product : ℕ) : ℝ :=
  (product : ℝ) / (reactant : ℝ)

def circuitGrossRatio : ℝ := grossStoichiometricRatio 2 (2 + 2)

def CircuitUniqueGlobalMaximum (xStar yStar zStar : ℝ) : Prop :=
  CircuitSteady xStar yStar zStar ∧
  (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → CircuitSteady x y z →
    circuitJ1 x y ≤ circuitJ1 xStar yStar) ∧
  (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → CircuitSteady x y z →
    circuitJ1 x y = circuitJ1 xStar yStar →
      x = xStar ∧ y = yStar ∧ z = zStar)

def circuitT : Fin 3 → Fin 3 → ℝ :=
  ![![0, 2, 0], ![1 / 2, 0, 1 / 2], ![0, 1, 0]]

def NoElementarySelfReturn {n : ℕ} (T : Fin n → Fin n → ℝ) : Prop :=
  ∀ i, T i i = 0

def HasPositiveRecyclingTwoCycle {n : ℕ}
    (T : Fin n → Fin n → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ 0 < T i j ∧ 0 < T j i

def CircuitDetailedBalance : Prop :=
  ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    6 * x = 5 * y ∧ 5 * y ^ 2 = 4 * x ^ 2 * z ^ 2 ∧
    6 * z ^ 2 = 5 * y

def CircuitSourceValid : Prop :=
  ((1 : ℤ) * 2 * 2 ≠ 0) ∧
  ((-1 : ℤ) * ((-2) * (-2) - 1 * 2) -
      2 * (1 * (-2) - 1 * 0) = 2) ∧
  ((-1 : ℤ) + 2 + 0 = 1) ∧
  ((1 : ℤ) - 2 + 1 = 0) ∧
  ((0 : ℤ) + 2 - 2 = 0) ∧
  (0 < (6 : ℝ) ∧ 0 < (5 : ℝ) ∧ 0 < (4 : ℝ)) ∧
  CircuitDetailedBalance

theorem circuit_netStoichiometry_sourceFacts :
    (-1 : ℤ) * ((-2) * (-2) - 1 * 2) -
        2 * (1 * (-2) - 1 * 0) = 2 ∧
    (-1 : ℤ) + 2 + 0 = 1 ∧
    (1 : ℤ) - 2 + 1 = 0 ∧
    (0 : ℤ) + 2 - 2 = 0 := by
  norm_num

theorem circuit_responseMatrix_zeroDiagonal :
    ∀ i, circuitT i i = 0 := by
  intro i
  fin_cases i <;> norm_num [circuitT]

theorem circuit_has_recyclingTwoCycle :
    HasPositiveRecyclingTwoCycle circuitT := by
  refine ⟨1, 2, by decide, ?_, ?_⟩
  · change (0 : ℝ) < 1 / 2
    norm_num
  · change (0 : ℝ) < 1
    norm_num

theorem circuit_no_elementary_selfReturn :
    NoElementarySelfReturn circuitT :=
  circuit_responseMatrix_zeroDiagonal

theorem circuit_detailedBalance : CircuitDetailedBalance := by
  let z : ℝ := Real.sqrt (9 / 5)
  have harg : (0 : ℝ) ≤ 9 / 5 := by norm_num
  have hzsq : z ^ 2 = 9 / 5 := by
    dsimp [z]
    exact (Real.sq_sqrt harg)
  have hz : 0 < z := by
    dsimp [z]
    positivity
  refine ⟨9 / 5, 54 / 25, z, by norm_num, by norm_num, hz, ?_, ?_, ?_⟩
  · norm_num
  · rw [hzsq]
    norm_num
  · rw [hzsq]
    norm_num

theorem circuit_isSourceValid : CircuitSourceValid := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num, by norm_num, ?_,
    circuit_detailedBalance⟩
  · norm_num
  · norm_num

theorem circuit_responseIdentity :
    let Fp : Fin 3 → ℝ := ![1, 12 / 5, 1]
    let Fm : Fin 3 → ℝ := ![6 / 5, 3, 6 / 5]
    ∀ j, (∑ i, Fp i * circuitT i j) = Fm j := by
  dsimp
  intro j
  fin_cases j <;> norm_num [Fin.sum_univ_succ, circuitT]

theorem circuit_optimumDerivativeBalance :
    (6 : ℝ) * 1 = 5 * (6 / 5) ∧
    (5 : ℝ) * (12 / 5) = 4 * 3 ∧
    (6 : ℝ) * 1 = 5 * (6 / 5) := by
  norm_num

theorem circuit_affinityViolation :
    (6 / 5 : ℝ) * (5 / 4) * (6 / 5) = 9 / 5 ∧ (9 / 5 : ℝ) < 2 := by
  norm_num

theorem circuit_exactAffinity : circuitExpAffinity 1 1 1 = 9 / 5 := by
  norm_num [circuitExpAffinity]

theorem circuit_exactGrossRatio : circuitGrossRatio = 2 := by
  norm_num [circuitGrossRatio, grossStoichiometricRatio]

theorem circuit_semanticAffinityViolation :
    circuitExpAffinity 1 1 1 < circuitGrossRatio := by
  rw [circuit_exactAffinity, circuit_exactGrossRatio]
  norm_num

theorem circuit_one_state_steady : CircuitSteady 1 1 1 := by
  norm_num [CircuitSteady, circuitJ1, circuitJ2, circuitJ3]

theorem circuit_polynomialCertificate (u J : ℝ) :
    5 * J - (6 * u - J) ^ 2 + 20 * u ^ 3 =
      4 * (u - 1) ^ 2 * (5 * u + 1) +
        (J - 1) * (12 * u + 4 - J) := by
  ring

theorem circuit_current_le_one
    (x y z J : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsteady : CircuitSteady x y z) (hJ : J = circuitJ1 x y) :
    J ≤ 1 := by
  have hxz : x = z ^ 2 := by
    rcases hsteady with ⟨h12, h23⟩
    have h13 : circuitJ1 x y = circuitJ3 y z := h12.trans h23
    dsimp [circuitJ1, circuitJ3] at h13
    linarith
  have hJeq : J = 6 * z ^ 2 - 5 * y := by
    rw [hJ, circuitJ1, hxz]
  have hJ2 : J = 5 * y ^ 2 - 4 * (z ^ 2) ^ 2 * z ^ 2 := by
    calc
      J = circuitJ1 x y := hJ
      _ = circuitJ2 x y z := hsteady.1
      _ = 5 * y ^ 2 - 4 * (z ^ 2) ^ 2 * z ^ 2 := by
        rw [circuitJ2, hxz]
  have hpoly : 5 * J - (6 * z ^ 2 - J) ^ 2 + 20 * (z ^ 2) ^ 3 = 0 := by
    nlinarith
  by_contra hle
  have hJgt : 1 < J := lt_of_not_ge hle
  have hu : 0 < z ^ 2 := sq_pos_of_pos hz
  have hJlt : J < 6 * z ^ 2 := by linarith
  have hfirst : 0 ≤ 4 * (z ^ 2 - 1) ^ 2 * (5 * z ^ 2 + 1) := by positivity
  have hlast : 0 < (J - 1) * (12 * z ^ 2 + 4 - J) := by
    apply mul_pos
    · linarith
    · linarith
  have hcert := circuit_polynomialCertificate (z ^ 2) J
  nlinarith

theorem circuit_current_eq_one_unique
    (x y z J : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsteady : CircuitSteady x y z) (hJ : J = circuitJ1 x y)
    (hEq : J = 1) : x = 1 ∧ y = 1 ∧ z = 1 := by
  have hxz : x = z ^ 2 := by
    rcases hsteady with ⟨h12, h23⟩
    have h13 : circuitJ1 x y = circuitJ3 y z := h12.trans h23
    dsimp [circuitJ1, circuitJ3] at h13
    linarith
  have hJeq : J = 6 * z ^ 2 - 5 * y := by
    rw [hJ, circuitJ1, hxz]
  have hJ2 : J = 5 * y ^ 2 - 4 * (z ^ 2) ^ 2 * z ^ 2 := by
    calc
      J = circuitJ1 x y := hJ
      _ = circuitJ2 x y z := hsteady.1
      _ = 5 * y ^ 2 - 4 * (z ^ 2) ^ 2 * z ^ 2 := by
        rw [circuitJ2, hxz]
  have hpoly : 5 * J - (6 * z ^ 2 - J) ^ 2 + 20 * (z ^ 2) ^ 3 = 0 := by
    nlinarith
  have hcert := circuit_polynomialCertificate (z ^ 2) J
  have hu : 0 < z ^ 2 := sq_pos_of_pos hz
  have hsquare : (z ^ 2 - 1) ^ 2 = 0 := by
    have hfactor : 0 < 5 * z ^ 2 + 1 := by positivity
    nlinarith [sq_nonneg (z ^ 2 - 1)]
  have hzsq : z ^ 2 = 1 := by nlinarith
  have hz1 : z = 1 := by nlinarith [sq_nonneg (z - 1)]
  have hx1 : x = 1 := by rw [hxz, hzsq]
  have hy1 : y = 1 := by nlinarith
  exact ⟨hx1, hy1, hz1⟩

theorem circuit_uniqueGlobalMaximum :
    CircuitSteady 1 1 1 ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → CircuitSteady x y z →
      circuitJ1 x y ≤ circuitJ1 1 1) ∧
    (∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → CircuitSteady x y z →
      circuitJ1 x y = circuitJ1 1 1 → x = 1 ∧ y = 1 ∧ z = 1) := by
  refine ⟨circuit_one_state_steady, ?_, ?_⟩
  · intro x y z hx hy hz hs
    have hle := circuit_current_le_one x y z (circuitJ1 x y) hx hy hz hs rfl
    norm_num [circuitJ1] at hle ⊢
    exact hle
  · intro x y z hx hy hz hs heq
    have hJ : circuitJ1 x y = 1 := by
      calc
        circuitJ1 x y = circuitJ1 1 1 := heq
        _ = 1 := by norm_num [circuitJ1]
    exact circuit_current_eq_one_unique x y z (circuitJ1 x y) hx hy hz hs rfl hJ

theorem circuit_uniqueGlobalMaximum_semantic :
    CircuitUniqueGlobalMaximum 1 1 1 := by
  exact circuit_uniqueGlobalMaximum

theorem zeroDiagonalSourceCounterexample :
    CircuitSourceValid ∧
    (∀ i, circuitT i i = 0) ∧
    CircuitUniqueGlobalMaximum 1 1 1 ∧
    circuitExpAffinity 1 1 1 = 9 / 5 ∧
    circuitGrossRatio = 2 ∧
    circuitExpAffinity 1 1 1 < circuitGrossRatio := by
  exact ⟨circuit_isSourceValid, circuit_responseMatrix_zeroDiagonal,
    circuit_uniqueGlobalMaximum_semantic, circuit_exactAffinity,
    circuit_exactGrossRatio, circuit_semanticAffinityViolation⟩

end
end OptimalAffinityCorrected

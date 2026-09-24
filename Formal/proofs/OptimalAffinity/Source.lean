import Mathlib

/-!
Literal source data for the two-species, two-reaction optimal-affinity
counterexample.  Reactant and product stoichiometries are retained separately,
so the catalytic product return in reaction 2 cannot be erased by passing too
early to net stoichiometry.
-/

namespace OptimalAffinity

abbrev Reaction := Fin 2

structure Network where
  xReactant : Reaction → ℕ
  yReactant : Reaction → ℕ
  xProduct : Reaction → ℕ
  yProduct : Reaction → ℕ
  kPlus : Reaction → ℝ
  kMinus : Reaction → ℝ

def forwardFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  N.kPlus r * x ^ N.xReactant r * y ^ N.yReactant r

def reverseFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  N.kMinus r * x ^ N.xProduct r * y ^ N.yProduct r

def netFlux (N : Network) (r : Reaction) (x y : ℝ) : ℝ :=
  forwardFlux N r x y - reverseFlux N r x y

def netX (N : Network) (r : Reaction) : ℤ :=
  (N.xProduct r : ℤ) - N.xReactant r

def netY (N : Network) (r : Reaction) : ℤ :=
  (N.yProduct r : ℤ) - N.yReactant r

def determinant (N : Network) : ℤ :=
  netX N 0 * netY N 1 - netX N 1 * netY N 0

def alpha (N : Network) : ℕ := N.xReactant 0 + N.xReactant 1
def beta (N : Network) : ℕ := N.xProduct 0 + N.xProduct 1
def yInput (N : Network) : ℕ := N.yReactant 0 + N.yReactant 1
def yOutput (N : Network) : ℕ := N.yProduct 0 + N.yProduct 1

def UnitProductionMode (N : Network) : Prop :=
  netX N 0 + netX N 1 = 1 ∧ netY N 0 + netY N 1 = 0

def DetailedBalanceExists (N : Network) : Prop :=
  ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
    ∀ r : Reaction, forwardFlux N r x y = reverseFlux N r x y

def SourceValid (N : Network) : Prop :=
  (∀ r : Reaction, 0 < N.kPlus r ∧ 0 < N.kMinus r) ∧
  determinant N ≠ 0 ∧
  UnitProductionMode N ∧
  0 < alpha N ∧ alpha N < beta N ∧
  yInput N = yOutput N ∧
  DetailedBalanceExists N

def HasCatalyticReaction (N : Network) : Prop :=
  ∃ r : Reaction, 0 < N.yReactant r ∧ 0 < N.yProduct r

structure EmbeddingMasses where
  x : ℕ
  y : ℕ
  f1 : ℕ
  w1 : ℕ
  f2 : ℕ
  w2 : ℕ

def PositiveMassConservingEmbedding (m : EmbeddingMasses) : Prop :=
  0 < m.x ∧ 0 < m.y ∧ 0 < m.f1 ∧ 0 < m.w1 ∧ 0 < m.f2 ∧ 0 < m.w2 ∧
  m.f1 + m.x = m.y + m.w1 ∧
  m.f2 + 2 * m.y = 2 * m.x + m.y + m.w2

def oa2x2 : Network where
  xReactant := ![1, 0]
  yReactant := ![0, 2]
  xProduct := ![0, 2]
  yProduct := ![1, 1]
  kPlus := ![3, 7]
  kMinus := ![2, 6]

def oa2x2Masses : EmbeddingMasses where
  x := 1
  y := 1
  f1 := 1
  w1 := 1
  f2 := 2
  w2 := 1

theorem oa2x2_literalStoichiometry :
    oa2x2.xReactant = ![1, 0] ∧ oa2x2.yReactant = ![0, 2] ∧
    oa2x2.xProduct = ![0, 2] ∧ oa2x2.yProduct = ![1, 1] := by
  simp [oa2x2]

theorem oa2x2_ratesPositive :
    ∀ r : Reaction, 0 < oa2x2.kPlus r ∧ 0 < oa2x2.kMinus r := by
  intro r
  fin_cases r <;> norm_num [oa2x2]

theorem oa2x2_netEntries :
    netX oa2x2 0 = -1 ∧ netX oa2x2 1 = 2 ∧
    netY oa2x2 0 = 1 ∧ netY oa2x2 1 = -1 := by
  norm_num [netX, netY, oa2x2]

theorem oa2x2_determinant : determinant oa2x2 = -1 := by
  norm_num [determinant, netX, netY, oa2x2]

theorem oa2x2_inverseWitness :
    (-1 : ℤ) * 1 + 2 * 1 = 1 ∧
    (-1 : ℤ) * 2 + 2 * 1 = 0 ∧
    (1 : ℤ) * 1 + (-1) * 1 = 0 ∧
    (1 : ℤ) * 2 + (-1) * 1 = 1 := by
  norm_num

theorem oa2x2_unitProductionMode : UnitProductionMode oa2x2 := by
  norm_num [UnitProductionMode, netX, netY, oa2x2]

theorem oa2x2_overallReaction :
    alpha oa2x2 = 1 ∧ beta oa2x2 = 2 ∧
    yInput oa2x2 = 2 ∧ yOutput oa2x2 = 2 := by
  norm_num [alpha, beta, yInput, yOutput, oa2x2]

theorem oa2x2_detailedBalance : DetailedBalanceExists oa2x2 := by
  refine ⟨7 / 4, 21 / 8, by norm_num, by norm_num, ?_⟩
  intro r
  fin_cases r <;> norm_num [forwardFlux, reverseFlux, oa2x2]

theorem oa2x2_hasCatalyticProductReturn : HasCatalyticReaction oa2x2 := by
  refine ⟨1, ?_⟩
  norm_num [HasCatalyticReaction, oa2x2]

theorem oa2x2_fullEmbedding_massConserving :
    PositiveMassConservingEmbedding oa2x2Masses := by
  norm_num [PositiveMassConservingEmbedding, oa2x2Masses]

theorem oa2x2_responseRecyclingEntry : (1 : ℝ) / 2 = 1 / 2 := by
  norm_num

theorem oa2x2_isSourceNetwork : SourceValid oa2x2 := by
  refine ⟨oa2x2_ratesPositive, ?_, oa2x2_unitProductionMode, ?_, ?_, ?_,
    oa2x2_detailedBalance⟩
  · rw [oa2x2_determinant]
    norm_num
  · norm_num [alpha, oa2x2]
  · norm_num [alpha, beta, oa2x2]
  · norm_num [yInput, yOutput, oa2x2]

end OptimalAffinity

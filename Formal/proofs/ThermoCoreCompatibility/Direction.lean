import proofs.ThermoCoreCompatibility.CoreFamily

/-! Direction potentials and exact signed-circuit obstruction certificates. -/

namespace ThermoCoreCompatibility

open scoped BigOperators

variable {Species Reaction Core : Type*}
  [DecidableEq Species] [DecidableEq Reaction]
  [Fintype Species] [Fintype Reaction] [Fintype Core]

namespace CoreFamily

variable {Q : ReversibleCRN Species Reaction}

def orientedDisplacement (F : CoreFamily (Core := Core) Q)
    (r : Reaction) (s : Species) : ℝ :=
  (F.orientation r : ℝ) * ((Q.reactant r s : ℝ) - (Q.product r s : ℝ))

def directionalAffinity (F : CoreFamily (Core := Core) Q)
    (μ : Species → ℝ) (r : Reaction) : ℝ :=
  ∑ s, F.orientedDisplacement r s * μ s

def DirectionCompatible (F : CoreFamily (Core := Core) Q) : Prop :=
  ∃ μ : Species → ℝ, ∀ r, 0 < F.directionalAffinity μ r

structure SignedCircuit (F : CoreFamily (Core := Core) Q) where
  weight : Reaction → ℝ
  nonnegative : ∀ r, 0 ≤ weight r
  nonzero : ∃ r, 0 < weight r
  kernel : ∀ s, ∑ r, weight r * F.orientedDisplacement r s = 0

omit [DecidableEq Species] [DecidableEq Reaction] [Fintype Core] in
theorem SignedCircuit.annihilatesPotential
    {F : CoreFamily (Core := Core) Q} (C : F.SignedCircuit) (μ : Species → ℝ) :
    ∑ r, C.weight r * F.directionalAffinity μ r = 0 := by
  simp only [directionalAffinity, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc]
  simp [← Finset.sum_mul, C.kernel]

omit [DecidableEq Species] [DecidableEq Reaction] [Fintype Core] in
theorem signedCircuit_not_directionCompatible
    (F : CoreFamily (Core := Core) Q) (C : F.SignedCircuit) :
    ¬ F.DirectionCompatible := by
  rintro ⟨μ, hμ⟩
  have hnonneg : ∀ r ∈ (Finset.univ : Finset Reaction),
      0 ≤ C.weight r * F.directionalAffinity μ r := by
    intro r _
    exact mul_nonneg (C.nonnegative r) (le_of_lt (hμ r))
  rcases C.nonzero with ⟨r, hr⟩
  have hpos : 0 < ∑ r, C.weight r * F.directionalAffinity μ r := by
    apply Finset.sum_pos'
    · exact hnonneg
    · exact ⟨r, Finset.mem_univ r, mul_pos hr (hμ r)⟩
  rw [C.annihilatesPotential μ] at hpos
  exact lt_irrefl 0 hpos

end CoreFamily

end ThermoCoreCompatibility

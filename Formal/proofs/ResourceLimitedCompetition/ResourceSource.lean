import proofs.ResourceLimitedCompetition.AffineGrowthGenerator

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy

/-- Fixed currently living identities, between division events. Division and its
complementary draw are separate population transitions, not encoded by this type. -/
structure JointState (K : ℕ) where
  resource : ℕ
  cells : Fin K → Compartment

def jointNext {K : ℕ} (s : JointState K) (j : Fin K) (r : Channel) : JointState K :=
  { resource := match r with
      | .inl _ => s.resource
      | .inr _ => s.resource-1
    cells := Function.update s.cells j (nextCompartment (s.cells j) r) }

noncomputable def jointRate {K : ℕ} (γ : ℝ) (Ω : ℕ)
    (s : JointState K) (j : Fin K) (r : Channel) : ℝ :=
  propensity (resourceCoefficient γ s.resource Ω) (s.cells j) r

noncomputable def jointGenerator {K : ℕ} (γ : ℝ) (Ω : ℕ)
    (f : JointState K → ℝ) (s : JointState K) : ℝ :=
  ∑ j, ∑ r, jointRate γ Ω s j r * (f (jointNext s j r)-f s)

theorem joint_rate_nonneg {K : ℕ} (γ : ℝ) (Ω : ℕ) (hγ : 0 ≤ γ)
    (s : JointState K) (j : Fin K) (r : Channel) : 0 ≤ jointRate γ Ω s j r := by
  apply propensity_nonneg
  unfold resourceCoefficient
  positivity

theorem resource_empty_growth_disabled {K : ℕ} (γ : ℝ) (Ω : ℕ)
    (s : JointState K) (j : Fin K) (hQ : s.resource=0) :
    jointRate γ Ω s j (.inr ()) = 0 := by
  simp [jointRate, propensity, resourceCoefficient, hQ]

theorem growth_rate_literal {K : ℕ} (γ : ℝ) (Ω : ℕ)
    (s : JointState K) (j : Fin K) :
    jointRate γ Ω s j (.inr ()) =
      γ*((s.resource : ℝ)/(Ω : ℝ))*((s.cells j).1 2 : ℝ) := rfl

/-- Endogenous resource dependence creates no extra term in a tagged observable. -/
theorem tagged_generator_binding {K : ℕ} (γ : ℝ) (Ω : ℕ)
    (s : JointState K) (j : Fin K) (f : Compartment → ℝ) :
    jointGenerator γ Ω (fun x => f (x.cells j)) s =
      compartmentGenerator (resourceCoefficient γ s.resource Ω) f (s.cells j) := by
  classical
  unfold jointGenerator
  rw [Finset.sum_eq_single j]
  · simp [jointNext, jointRate, compartmentGenerator]
  · intro b _ hb
    have hjb : j ≠ b := Ne.symm hb
    simp [jointNext, Function.update_of_ne hjb]
  · simp

theorem other_cell_zero {K : ℕ} (s : JointState K) (j b : Fin K)
    (h : j ≠ b) (r : Channel) (f : Compartment → ℝ) :
    f ((jointNext s b r).cells j)-f (s.cells j)=0 := by
  simp [jointNext, Function.update_of_ne h]

end ResourceLimitedCompetition

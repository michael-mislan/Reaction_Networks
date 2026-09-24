import proofs.RandomViability.QuietPathComparison
import proofs.RandomViability.JumpRewardPaths

namespace RandomViability
open Classical FiniteCopy
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

theorem labeledUniformize_prob_domination (R M : FiniteJumpModel α β)
    (q0 q1 : NNReal) (h0 : 0 < (q0 : ℝ)) (h1 : 0 < (q1 : ℝ))
    (hb0 : ∀ x, R.total x ≤ q0) (hb1 : ∀ x, M.total x ≤ q1)
    (hrate : ∀ x b, R.rate x b ≤ M.rate x b)
    (hgap : ∀ x, M.total x ≤ R.total x + ((q1 : ℝ)-q0))
    (x : α) (b : Option β) :
    ((q0 : ℝ)/q1)*(labeledUniformize R q0 h0 hb0).prob x b ≤
      (labeledUniformize M q1 h1 hb1).prob x b := by
  cases b with
  | none =>
    change ((q0 : ℝ)/q1)*(1-R.total x/q0) ≤ 1-M.total x/q1
    have he0 : ((q0 : ℝ)/q1)*(1-R.total x/q0) = ((q0 : ℝ)-R.total x)/q1 := by field_simp
    have he1 : 1-M.total x/q1 = ((q1 : ℝ)-M.total x)/q1 := by field_simp
    rw [he0, he1]
    apply div_le_div_of_nonneg_right _ h1.le
    linarith [hgap x]
  | some b =>
    change ((q0 : ℝ)/q1)*(R.rate x b/q0) ≤ M.rate x b/q1
    have he : ((q0 : ℝ)/q1)*(R.rate x b/q0) = R.rate x b/q1 := by field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (hrate x b) h1.le

/-- Extra state-dependent reactions cost at most the exponential clock gap
for any event on shared labeled paths. No event/hazard independence is assumed. -/
theorem jump_quiet_event_lower (R M : FiniteJumpModel α β)
    (q0 q1 : NNReal) (h0 : 0 < (q0 : ℝ)) (h1 : 0 < (q1 : ℝ))
    (hb0 : ∀ x, R.total x ≤ q0) (hb1 : ∀ x, M.total x ≤ q1)
    (hnext : ∀ x b, M.next x b = R.next x b)
    (hrate : ∀ x b, R.rate x b ≤ M.rate x b)
    (hgap : ∀ x, M.total x ≤ R.total x + ((q1 : ℝ)-q0))
    (t : NNReal) (x : α) (E : (n : ℕ) → RewardPath (Option β) n → Prop) :
    Real.exp (-(((q1 : ℝ)-q0)*t)) *
      (labeledUniformize R q0 h0 hb0).poissonEventMass (q0*t) x E ≤
        (labeledUniformize M q1 h1 hb1).poissonEventMass (q1*t) x E := by
  have hn : ∀ y b, (labeledUniformize M q1 h1 hb1).next y b =
      (labeledUniformize R q0 h0 hb0).next y b := by
    intro y b
    cases b with
    | none => rfl
    | some b => exact hnext y b
  have hp : ∀ y b, ((q0/q1 : NNReal) : ℝ)*(labeledUniformize R q0 h0 hb0).prob y b ≤
      (labeledUniformize M q1 h1 hb1).prob y b := by
    intro y b
    exact labeledUniformize_prob_domination R M q0 q1 h0 h1 hb0 hb1 hrate hgap y b
  have hh := FiniteLabeledKernel.poissonEventMass_domination
    (labeledUniformize R q0 h0 hb0) (labeledUniformize M q1 h1 hb1) (q0/q1) (q1*t) hn hp x E
  have ht : (q0/q1)*(q1*t) = q0*t := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_div]
    field_simp
  have he : (((q0/q1 : NNReal) : ℝ)-1)*((q1*t : NNReal) : ℝ) = -(((q1 : ℝ)-q0)*t) := by
    simp only [NNReal.coe_mul, NNReal.coe_div]
    field_simp
    ring
  simpa only [ht, he] using hh

end
end RandomViability



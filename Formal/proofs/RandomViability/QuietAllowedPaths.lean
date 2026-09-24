import proofs.RandomViability.QuietJumpComparison

namespace RandomViability
open Classical FiniteCopy
noncomputable section
namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

def pathAllowed (A : β → Prop) : (n : ℕ) → RewardPath β n → Prop
  | 0, _ => True
  | n+1, p => A p.1 ∧ pathAllowed A n p.2

theorem pathWeight_eq_zero_of_not_allowed (K : FiniteLabeledKernel α β)
    (A : β → Prop) (hz : ∀ x b, ¬ A b → K.prob x b = 0)
    (n : ℕ) (x : α) (p : RewardPath β n) (h : ¬ pathAllowed A n p) :
    K.pathWeight n x p = 0 := by
  induction n generalizing x with
  | zero => exact False.elim (h trivial)
  | succ n ih =>
    change K.prob x p.1 * K.pathWeight n (K.next x p.1) p.2 = 0
    by_cases ha : A p.1
    · have ht : ¬ pathAllowed A n p.2 := fun hh => h ⟨ha, hh⟩
      rw [ih _ p.2 ht, mul_zero]
    · rw [hz x p.1 ha, zero_mul]

theorem pathEventMass_restrict_allowed (K : FiniteLabeledKernel α β)
    (A : β → Prop) (hz : ∀ x b, ¬ A b → K.prob x b = 0)
    (n : ℕ) (x : α) (E : RewardPath β n → Prop) :
    K.pathEventMass n x (fun p => E p ∧ pathAllowed A n p) = K.pathEventMass n x E := by
  unfold pathEventMass
  apply Finset.sum_congr rfl
  intro p _
  by_cases ha : pathAllowed A n p
  · simp only [ha, and_true]
  · simp only [ha, and_false, if_false]
    split_ifs
    · exact (K.pathWeight_eq_zero_of_not_allowed A hz n x p ha).symm
    · rfl

theorem poissonEventMass_restrict_allowed (K : FiniteLabeledKernel α β)
    (A : β → Prop) (hz : ∀ x b, ¬ A b → K.prob x b = 0)
    (t : NNReal) (x : α) (E : (n : ℕ) → RewardPath β n → Prop) :
    K.poissonEventMass t x (fun n p => E n p ∧ pathAllowed A n p) = K.poissonEventMass t x E := by
  unfold poissonEventMass
  apply tsum_congr
  intro n
  rw [K.pathEventMass_restrict_allowed A hz]

end FiniteLabeledKernel

theorem jump_quiet_allowed_event_lower {α β : Type*} [Fintype α] [Fintype β]
    (R M : FiniteJumpModel α β)
    (q0 q1 : NNReal) (h0 : 0 < (q0 : ℝ)) (h1 : 0 < (q1 : ℝ))
    (hb0 : ∀ x, R.total x ≤ q0) (hb1 : ∀ x, M.total x ≤ q1)
    (hnext : ∀ x b, M.next x b = R.next x b)
    (hrate : ∀ x b, R.rate x b ≤ M.rate x b)
    (hgap : ∀ x, M.total x ≤ R.total x + ((q1 : ℝ)-q0))
    (A : Option β → Prop)
    (hz : ∀ x b, ¬ A b → (labeledUniformize R q0 h0 hb0).prob x b = 0)
    (t : NNReal) (x : α) (E : (n : ℕ) → RewardPath (Option β) n → Prop) :
    Real.exp (-(((q1 : ℝ)-q0)*t)) *
      (labeledUniformize R q0 h0 hb0).poissonEventMass (q0*t) x E ≤
        (labeledUniformize M q1 h1 hb1).poissonEventMass (q1*t) x
          (fun n p => E n p ∧ FiniteLabeledKernel.pathAllowed A n p) := by
  have hh := jump_quiet_event_lower R M q0 q1 h0 h1 hb0 hb1 hnext hrate hgap t x
    (fun n p => E n p ∧ FiniteLabeledKernel.pathAllowed A n p)
  rw [FiniteLabeledKernel.poissonEventMass_restrict_allowed _ A hz] at hh
  exact hh
end
end RandomViability

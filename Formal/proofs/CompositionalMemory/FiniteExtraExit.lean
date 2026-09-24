import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy
noncomputable section

/-- Add a monitored failure channel. In applications `dead` is absorbing.
This permits a conservative certificate that rejects every reverse-growth
event, without solving a backward equation over decreasing volume layers. -/
def withExtraExit {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (dead : α) (κ : α → ℝ) (hk : ∀ x, 0 ≤ κ x) :
    FiniteJumpModel α (Option β) where
  next x r := r.elim dead (M.next x)
  rate x r := r.elim (κ x) (M.rate x)
  nonneg x r := by
    cases r with
    | none => exact hk x
    | some r => exact M.nonneg x r

theorem withExtraExit_generator {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (dead : α) (κ : α → ℝ) (hk : ∀ x, 0 ≤ κ x)
    (f : α → ℝ) (x : α) :
    (withExtraExit M dead κ hk).generator f x=M.generator f x+κ x*(f dead-f x) := by
  simp only [FiniteJumpModel.generator,withExtraExit,Fintype.sum_option,Option.elim]
  ring

/-- Killing loses at most its rate from a return subsolution bounded above by
one, while improving a nonnegative time witness. This is a quantitative bound,
not a qualitative continuity assertion. -/
theorem extra_exit_generators {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (dead : α) (κ : α → ℝ) (hk : ∀ x, 0 ≤ κ x)
    (v w : α → ℝ) (δ η s K : ℝ)
    (hvdead : v dead=0) (hwdead : w dead=0)
    (hvu : ∀ x, v x ≤ 1) (hwn : ∀ x, 0 ≤ w x) (hκ : ∀ x, κ x ≤ K)
    (hv : ∀ x, -δ ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -s*w x+η) :
    (∀ x, -(δ+K) ≤ (withExtraExit M dead κ hk).generator v x) ∧
    (∀ x, (withExtraExit M dead κ hk).generator w x ≤ -s*w x+η) := by
  constructor
  · intro x
    rw [withExtraExit_generator,hvdead]
    have hm := mul_le_mul_of_nonneg_left (hvu x) (hk x)
    nlinarith [hv x,hκ x]
  · intro x
    rw [withExtraExit_generator,hwdead]
    have hm := mul_nonneg (hk x) (hwn x)
    nlinarith [hw x]

theorem extra_exit_deadline {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (dead : α) (κ : α → ℝ) (hk : ∀ x, 0 ≤ κ x)
    (h v w : α → ℝ) (δ η s K : ℝ) (t : NNReal)
    (hs : 0 < s) (hη : 0 ≤ η)
    (hvdead : v dead=0) (hwdead : w dead=0)
    (hvu : ∀ x, v x ≤ 1) (hwn : ∀ x, 0 ≤ w x) (hκ : ∀ x, κ x ≤ K)
    (hv : ∀ x, -δ ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -s*w x+η)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α) :
    v x-(t : ℝ)*(δ+K)-Real.exp (-s*(t : ℝ))*w x-η/s ≤
      finiteTimeExpectation (withExtraExit M dead κ hk) t h x := by
  have hh := extra_exit_generators M dead κ hk v w δ η s K hvdead hwdead hvu hwn hκ hv hw
  exact finite_deadline_residual_certificate (withExtraExit M dead κ hk) t h v w s (δ+K) η
    hs hη hh.1 hh.2 hcover x

end
end CompositionalMemory

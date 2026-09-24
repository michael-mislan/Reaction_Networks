import proofs.CompositionalMemory.ReversibleBirthDeadline
import proofs.CompositionalMemory.FiniteExtraExit
import proofs.CompositionalMemory.FiniteEventQuota

namespace CompositionalMemory
open FiniteCopy

/-- Exact combined loss budget. This lemma is only the analytic implication;
the model-specific rate bound and the actual-source encoding must be supplied. -/
theorem reversible_monitored_deadline {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (dead : α) (κ : α → ℝ)
    (hk : ∀ x, 0 ≤ κ x) (h v w : α → ℝ)
    (hvdead : v dead=0) (hwdead : w dead=0)
    (hvu : ∀ x, v x ≤ 1) (hwn : ∀ x, 0 ≤ w x)
    (hκ : ∀ x, κ x ≤ 53/1250000)
    (hrate : ∀ x, (withExtraExit M dead κ hk).total x ≤ 4000000)
    (hv : ∀ x, -(2/1000000 : ℝ) ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -(5/8 : ℝ)*w x+1/50000)
    (hcover : ∀ x, v x ≤ h x+w x) (x : α)
    (hbirth : (495550 : ℝ) ≤ 500000*v x-2*w x) :
    (9901/10000 : ℝ) ≤ finiteTimeExpectation
      (eventBudgetModel (withExtraExit M dead κ hk) 100000000) 20
      (budgetObservable 100000000 h) (x,0) := by
  have hg := extra_exit_generators M dead κ hk v w (2/1000000) (1/50000)
    (5/8) (53/1250000) hvdead hwdead hvu hwn hκ hv hw
  have hh := event_quota_deadline (withExtraExit M dead κ hk)
    h v w (2/1000000+53/1250000) (1/50000) (5/8)
    (by norm_num) (by norm_num) (by norm_num)
    hvu hwn hrate hg.1 hg.2 hcover x
  norm_num at hh
  have ht := mul_le_mul_of_nonneg_right wide_deadline_exp_bound (hwn x)
  nlinarith only [hh,ht,hbirth]

end CompositionalMemory

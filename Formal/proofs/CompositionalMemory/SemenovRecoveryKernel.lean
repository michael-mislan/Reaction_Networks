import proofs.CompositionalMemory.SemenovBothDaughters
import proofs.CompositionalMemory.FiniteLineageKernel

namespace CompositionalMemory.Semenov
open MeasureTheory FiniteCopy HeritableCompositions

theorem finite_time_one_sub {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (t : NNReal) (f : α → ℝ) (s : α) :
    finiteTimeExpectation M t (fun z => 1-f z) s=1-finiteTimeExpectation M t f s := by
  have hc : finiteTimeExpectation M t (fun _ => (1 : ℝ)) s=1 := by
    obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
    rw [finite_time_eq_uniformized M q t hq hb]
    exact poisson_constant _ _ 1 s
  simp only [finiteTimeExpectation,Matrix.mulVec,dotProduct,mul_sub,Finset.sum_sub_distrib] at hc ⊢
  rw [hc]

abbrev GoodRecoveryState (high : Bool) :=
  {s : ReactorState recoveryCountCap recoveryFeedQuota // recoveryFailure high s=0}

noncomputable instance goodRecoveryState_fintype (high : Bool) : Fintype (GoodRecoveryState high) :=
  Fintype.ofFinite _

def recoveryStateCounts : ReactorState recoveryCountCap recoveryFeedQuota → Fin 8 → ℕ
  | none => fun _ => 0
  | some (n,_) => fun j => (n j).val

theorem good_state_parent (high : Bool) (x : GoodRecoveryState high) :
    GoodRecoveryParent high (recoveryStateCounts x.val) := by
  classical
  rcases x with ⟨s,hs⟩
  cases s with
  | none => norm_num [recoveryFailure] at hs
  | some p =>
    by_contra hn
    change ¬GoodRecoveryParent high (fun j => (p.1 j).val) at hn
    simp only [recoveryFailure,if_neg hn] at hs
    norm_num at hs

theorem recovery_failure_one_of_ne_zero (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota)
    (hs : recoveryFailure high s ≠ 0) : recoveryFailure high s=1 := by
  classical
  cases s with
  | none => rfl
  | some p =>
    simp only [recoveryFailure] at hs ⊢
    split_ifs at hs ⊢ <;> norm_num at *

theorem good_state_indicator_sum (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    (∑ y : GoodRecoveryState high,if s=y.val then (1 : ℝ) else 0)=1-recoveryFailure high s := by
  classical
  by_cases hs : recoveryFailure high s=0
  · rw [Finset.sum_eq_single (⟨s,hs⟩ : GoodRecoveryState high)]
    · simp [hs]
    · intro y _ hy
      have hne : s ≠ y.val := by
        intro he
        apply hy
        exact Subtype.ext he.symm
      simp only [if_neg hne]
    · simp
  · have hne (y : GoodRecoveryState high) : s ≠ y.val := by
      intro he
      apply hs
      rw [he]
      exact y.property
    simp only [hne,if_false,Finset.sum_const_zero,recovery_failure_one_of_ne_zero high s hs,sub_self]

noncomputable def recoveryTransition (s y : ReactorState recoveryCountCap recoveryFeedQuota) : ℝ :=
  finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
    500 (fun z => if z=y then 1 else 0) s

theorem recovery_transition_bounds (s y : ReactorState recoveryCountCap recoveryFeedQuota) :
    0 ≤ recoveryTransition s y ∧ recoveryTransition s y ≤ 1 := by
  apply finite_time_bounds
  intro z
  split_ifs <;> norm_num

theorem recovery_transition_good_sum (high : Bool) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    (∑ y : GoodRecoveryState high,recoveryTransition s y.val)=
      1-finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
        500 (recoveryFailure high) s := by
  classical
  let M := nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _)
  have hsum : (∑ y : GoodRecoveryState high,recoveryTransition s y.val)=
      finiteTimeExpectation M 500 (fun z => 1-recoveryFailure high z) s := by
    unfold recoveryTransition finiteTimeExpectation
    simp only [Matrix.mulVec,dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,good_state_indicator_sum]
    rfl
  exact hsum.trans (finite_time_one_sub M 500 (recoveryFailure high) s)

end CompositionalMemory.Semenov

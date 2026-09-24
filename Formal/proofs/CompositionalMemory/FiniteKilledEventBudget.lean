import proofs.CompositionalMemory.FiniteEventBudget

namespace CompositionalMemory
open FiniteCopy
noncomputable section

/-- A single cemetery state makes this counter compatible with safe-history
encoding of a countable source. The quota event is rejected. -/
def killedBudgetNext {σ β : Type*} [Fintype σ] [Fintype β]
    (M : FiniteJumpModel (Option σ) β) (J : Nat) :
    Option (σ × Fin J) → β → Option (σ × Fin J)
  | none,_ => none
  | some (a,c),r =>
    if hc : c.val+1<J then (M.next (some a) r).map (fun b => (b,⟨c.val+1,hc⟩)) else none

def killedBudgetModel {σ β : Type*} [Fintype σ] [Fintype β]
    (M : FiniteJumpModel (Option σ) β) (J : Nat) :
    FiniteJumpModel (Option (σ × Fin J)) β where
  next := killedBudgetNext M J
  rate s r := s.elim 0 (fun z => M.rate (some z.1) r)
  nonneg s r := by cases s with | none => exact le_rfl | some z => exact M.nonneg _ r

def killedBudgetValue {σ : Type*} (J : Nat) (v : Option σ → ℝ) : Option (σ × Fin J) → ℝ
  | none => 0
  | some (a,c) => v (some a)-(c.val : ℝ)/(J : ℝ)

def killedBudgetObservable {σ : Type*} (J : Nat) (w : Option σ → ℝ) : Option (σ × Fin J) → ℝ
  | none => 0
  | some (a,_) => w (some a)

theorem killed_budget_next_lower {σ β : Type*} [Fintype σ] [Fintype β]
    (M : FiniteJumpModel (Option σ) β) (J : Nat) (hJ : 0 < J)
    (v : Option σ → ℝ) (hv0 : v none=0) (hvu : ∀ z, v z ≤ 1)
    (a : σ) (c : Fin J) (r : β) :
    v (M.next (some a) r)-((c.val+1 : Nat) : ℝ)/(J : ℝ) ≤
      killedBudgetValue J v (killedBudgetNext M J (some (a,c)) r) := by
  by_cases hc : c.val+1<J
  · simp only [killedBudgetNext,hc,dif_pos]
    cases hn : M.next (some a) r with
    | none => simp [killedBudgetValue,hv0]; positivity
    | some b => simp [killedBudgetValue]
  · have he : c.val+1=J := by have hh := c.isLt; omega
    simp only [killedBudgetNext]
    rw [dif_neg hc]
    change v (M.next (some a) r)-((c.val+1 : Nat) : ℝ)/(J : ℝ) ≤ 0
    rw [he,div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hJ))]
    exact sub_nonpos.mpr (hvu _)

theorem killed_budget_next_upper {σ β : Type*} [Fintype σ] [Fintype β]
    (M : FiniteJumpModel (Option σ) β) (J : Nat) (w : Option σ → ℝ)
    (hwn : ∀ z, 0 ≤ w z) (a : σ) (c : Fin J) (r : β) :
    killedBudgetObservable J w (killedBudgetNext M J (some (a,c)) r) ≤ w (M.next (some a) r) := by
  simp only [killedBudgetNext]
  split_ifs
  · cases hn : M.next (some a) r with
    | none => exact hwn none
    | some b => exact le_rfl
  · exact hwn _

theorem killed_budget_generators {σ β : Type*} [Fintype σ] [Fintype β]
    [DecidableEq σ] (M : FiniteJumpModel (Option σ) β) (J : Nat) (hJ : 0 < J)
    (v w : Option σ → ℝ) (δ η s L : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hv0 : v none=0) (hvu : ∀ z, v z ≤ 1) (hwn : ∀ z, 0 ≤ w z)
    (hrate : ∀ z, M.total z ≤ L)
    (hv : ∀ z, -δ ≤ M.generator v z) (hw : ∀ z, M.generator w z ≤ -s*w z+η) :
    (∀ z, -(δ+L/(J : ℝ)) ≤ (killedBudgetModel M J).generator (killedBudgetValue J v) z) ∧
    (∀ z, (killedBudgetModel M J).generator (killedBudgetObservable J w) z ≤
      -s*killedBudgetObservable J w z+η) := by
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  constructor
  · intro z
    cases z with
    | none =>
      simp only [FiniteJumpModel.generator,killedBudgetModel,Option.elim,
        zero_mul,Finset.sum_const_zero]
      exact neg_nonpos.mpr (add_nonneg hδ (div_nonneg hL hJr.le))
    | some z =>
      rcases z with ⟨a,c⟩
      have hs : M.generator v (some a)-M.total (some a)/(J : ℝ) ≤
          (killedBudgetModel M J).generator (killedBudgetValue J v) (some (a,c)) := by
        calc
          _ = ∑ r,M.rate (some a) r*((v (M.next (some a) r)-v (some a))-1/(J : ℝ)) := by
            simp only [FiniteJumpModel.generator,FiniteJumpModel.total,mul_sub,
              Finset.sum_sub_distrib,mul_one_div,Finset.sum_div]
          _ ≤ _ := by
            unfold FiniteJumpModel.generator
            apply Finset.sum_le_sum
            intro r _
            simp only [killedBudgetModel,Option.elim,killedBudgetValue]
            apply mul_le_mul_of_nonneg_left _ (M.nonneg _ r)
            have hn := killed_budget_next_lower M J hJ v hv0 hvu a c r
            push_cast at hn
            rw [add_div] at hn
            dsimp only [killedBudgetValue] at hn
            linarith
      have hd := div_le_div_of_nonneg_right (hrate (some a)) hJr.le
      linarith [hv (some a)]
  · intro z
    cases z with
    | none => simpa [FiniteJumpModel.generator,killedBudgetModel,killedBudgetObservable] using hη
    | some z =>
      rcases z with ⟨a,c⟩
      have hs : (killedBudgetModel M J).generator (killedBudgetObservable J w) (some (a,c)) ≤
          M.generator w (some a) := by
        unfold FiniteJumpModel.generator
        apply Finset.sum_le_sum
        intro r _
        simp only [killedBudgetModel,Option.elim,killedBudgetObservable]
        apply mul_le_mul_of_nonneg_left _ (M.nonneg _ r)
        exact sub_le_sub_right (killed_budget_next_upper M J w hwn a c r) _
      exact hs.trans (hw (some a))

theorem killed_budget_deadline {σ β : Type*} [Fintype σ] [Fintype β]
    [DecidableEq σ] (M : FiniteJumpModel (Option σ) β) (J : Nat) (hJ : 0 < J)
    (h v w : Option σ → ℝ) (δ η s L : ℝ) (t : NNReal)
    (hs : 0 < s) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hv0 : v none=0) (hvu : ∀ z, v z ≤ 1) (hwn : ∀ z, 0 ≤ w z)
    (hrate : ∀ z, M.total z ≤ L)
    (hv : ∀ z, -δ ≤ M.generator v z) (hw : ∀ z, M.generator w z ≤ -s*w z+η)
    (hcover : ∀ z, v z ≤ h z+w z) (a : σ) :
    v (some a)-(t : ℝ)*(δ+L/(J : ℝ))-Real.exp (-s*(t : ℝ))*w (some a)-η/s ≤
      finiteTimeExpectation (killedBudgetModel M J) t (killedBudgetObservable J h)
        (some (a,⟨0,hJ⟩)) := by
  have hg := killed_budget_generators M J hJ v w δ η s L hδ hη hL hv0 hvu hwn hrate hv hw
  have hc (z : Option (σ × Fin J)) : killedBudgetValue J v z ≤
      killedBudgetObservable J h z+killedBudgetObservable J w z := by
    cases z with
    | none => norm_num [killedBudgetValue,killedBudgetObservable]
    | some z =>
      rcases z with ⟨a,c⟩
      change v (some a)-(c.val : ℝ)/(J : ℝ) ≤ h (some a)+w (some a)
      have hn : 0 ≤ (c.val : ℝ)/(J : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith [hcover (some a)]
  have hh := finite_deadline_residual_certificate (killedBudgetModel M J) t
    (killedBudgetObservable J h) (killedBudgetValue J v) (killedBudgetObservable J w)
    s (δ+L/(J : ℝ)) η hs hη hg.1 hg.2 hc (some (a,⟨0,hJ⟩))
  simpa [killedBudgetValue,killedBudgetObservable] using hh

end
end CompositionalMemory

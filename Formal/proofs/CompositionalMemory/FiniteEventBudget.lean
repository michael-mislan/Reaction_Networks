import proofs.CompositionalMemory.FiniteDeadlineCertificate

namespace CompositionalMemory
open FiniteCopy
noncomputable section

def budgetIndex (J : Nat) (c : Fin (J+1)) : Fin (J+1) :=
  ⟨min (c.val+1) J, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Stop and reject the history at its J-th model event. Counting self-loops
overestimates chemical consumption and is therefore conservative. -/
def eventBudgetModel {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (J : Nat) : FiniteJumpModel (α × Fin (J+1)) β where
  next s r := if s.2.val<J then (M.next s.1 r,budgetIndex J s.2) else s
  rate s r := if s.2.val<J then M.rate s.1 r else 0
  nonneg s r := by split_ifs; exact M.nonneg s.1 r; exact le_rfl

def budgetValue {α : Type*} (J : Nat) (v : α → ℝ) (s : α × Fin (J+1)) : ℝ :=
  if s.2.val<J then v s.1-(s.2.val : ℝ)/(J : ℝ) else 0

def budgetObservable {α : Type*} (J : Nat) (v : α → ℝ) (s : α × Fin (J+1)) : ℝ :=
  if s.2.val<J then v s.1 else 0

theorem budget_next_lower {α : Type*} (J : Nat) (hJ : 0 < J) (v : α → ℝ)
    (hvu : ∀ a, v a ≤ 1) (a : α) (c : Fin (J+1)) (hc : c.val<J) :
    v a-((c.val+1 : Nat) : ℝ)/(J : ℝ) ≤ budgetValue J v (a,budgetIndex J c) := by
  have he : min (c.val+1) J=c.val+1 := Nat.min_eq_left (by omega)
  simp only [budgetValue,budgetIndex,he]
  by_cases hh : c.val+1<J
  · rw [if_pos hh]
  · have hj : c.val+1=J := by omega
    rw [if_neg hh,hj,div_self (Nat.cast_ne_zero.mpr (by omega))]
    exact sub_nonpos.mpr (hvu a)

theorem budget_next_upper {α : Type*} (J : Nat) (w : α → ℝ)
    (hwn : ∀ a, 0 ≤ w a) (a : α) (c : Fin (J+1)) :
    budgetObservable J w (a,budgetIndex J c) ≤ w a := by
  unfold budgetObservable
  split_ifs
  · exact le_rfl
  · exact hwn a

/-- The loss from a finite event budget is L/J per unit time. At the last
event, zero is above the corrected continuation because the original value
is at most one. No state-count enumeration is used. -/
theorem event_budget_generators {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (J : Nat) (hJ : 0 < J) (v w : α → ℝ)
    (δ η s L : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hvu : ∀ a, v a ≤ 1) (hwn : ∀ a, 0 ≤ w a) (hrate : ∀ a, M.total a ≤ L)
    (hv : ∀ a, -δ ≤ M.generator v a) (hw : ∀ a, M.generator w a ≤ -s*w a+η) :
    (∀ z, -(δ+L/(J : ℝ)) ≤ (eventBudgetModel M J).generator (budgetValue J v) z) ∧
    (∀ z, (eventBudgetModel M J).generator (budgetObservable J w) z ≤
      -s*budgetObservable J w z+η) := by
  have hJr : 0 < (J : ℝ) := Nat.cast_pos.mpr hJ
  constructor
  · rintro ⟨a,c⟩
    by_cases hc : c.val<J
    · have hsum : M.generator v a-M.total a/(J : ℝ) ≤
          (eventBudgetModel M J).generator (budgetValue J v) (a,c) := by
        calc
          _ = ∑ r,M.rate a r*((v (M.next a r)-v a)-1/(J : ℝ)) := by
            simp only [FiniteJumpModel.generator,FiniteJumpModel.total,mul_sub,
              Finset.sum_sub_distrib,mul_one_div,Finset.sum_div]
          _ ≤ _ := by
            unfold FiniteJumpModel.generator
            apply Finset.sum_le_sum
            intro r _
            simp only [eventBudgetModel,hc,if_true]
            apply mul_le_mul_of_nonneg_left _ (M.nonneg a r)
            have hn := budget_next_lower J hJ v hvu (M.next a r) c hc
            have he : budgetValue J v (a,c)=v a-(c.val : ℝ)/(J : ℝ) := if_pos hc
            rw [he]
            push_cast at hn
            rw [add_div] at hn
            linarith
      have hd := div_le_div_of_nonneg_right (hrate a) hJr.le
      linarith [hv a]
    · have hz : (eventBudgetModel M J).generator (budgetValue J v) (a,c)=0 := by
        simp [FiniteJumpModel.generator,eventBudgetModel,hc]
      rw [hz]
      exact neg_nonpos.mpr (add_nonneg hδ (div_nonneg hL hJr.le))
  · rintro ⟨a,c⟩
    by_cases hc : c.val<J
    · have hsum : (eventBudgetModel M J).generator (budgetObservable J w) (a,c) ≤
          M.generator w a := by
        unfold FiniteJumpModel.generator
        apply Finset.sum_le_sum
        intro r _
        simp only [eventBudgetModel,hc,if_true]
        apply mul_le_mul_of_nonneg_left _ (M.nonneg a r)
        have hn := budget_next_upper J w hwn (M.next a r) c
        have he : budgetObservable J w (a,c)=w a := if_pos hc
        rw [he]
        exact sub_le_sub_right hn _
      have he : budgetObservable J w (a,c)=w a := if_pos hc
      rw [he]
      exact hsum.trans (hw a)
    · simpa [FiniteJumpModel.generator,eventBudgetModel,budgetObservable,hc] using hη

theorem event_budget_deadline {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (M : FiniteJumpModel α β) (J : Nat) (hJ : 0 < J) (h v w : α → ℝ)
    (δ η s L : ℝ) (t : NNReal) (hs : 0 < s)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (hvu : ∀ a, v a ≤ 1) (hwn : ∀ a, 0 ≤ w a) (hrate : ∀ a, M.total a ≤ L)
    (hv : ∀ a, -δ ≤ M.generator v a) (hw : ∀ a, M.generator w a ≤ -s*w a+η)
    (hcover : ∀ a, v a ≤ h a+w a) (a : α) :
    v a-(t : ℝ)*(δ+L/(J : ℝ))-Real.exp (-s*(t : ℝ))*w a-η/s ≤
      finiteTimeExpectation (eventBudgetModel M J) t (budgetObservable J h) (a,0) := by
  have hg := event_budget_generators M J hJ v w δ η s L hδ hη hL hvu hwn hrate hv hw
  have hc (z : α × Fin (J+1)) : budgetValue J v z ≤
      budgetObservable J h z+budgetObservable J w z := by
    by_cases hz : z.2.val<J
    · simp only [budgetValue,budgetObservable,hz,if_true]
      have hn : 0 ≤ (z.2.val : ℝ)/(J : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      linarith [hcover z.1]
    · simp [budgetValue,budgetObservable,hz]
  have hh := finite_deadline_residual_certificate (eventBudgetModel M J) t
    (budgetObservable J h) (budgetValue J v) (budgetObservable J w) s (δ+L/(J : ℝ)) η
    hs hη hg.1 hg.2 hc (a,0)
  simpa [budgetValue,budgetObservable,hJ] using hh

end
end CompositionalMemory

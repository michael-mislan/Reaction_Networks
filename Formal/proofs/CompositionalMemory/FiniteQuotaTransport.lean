import proofs.CompositionalMemory.FiniteEventQuota
import proofs.CompositionalMemory.FiniteKilledEventBudget

namespace CompositionalMemory
open FiniteCopy
noncomputable section

theorem finite_time_generator_map {α γ β δ : Type*}
    [Fintype α] [Fintype γ] [Fintype β] [Fintype δ] [DecidableEq α] [DecidableEq γ]
    (M : FiniteJumpModel α β) (N : FiniteJumpModel γ δ) (π : α → γ)
    (hgen : ∀ f x, M.generator (fun z => f (π z)) x=N.generator f (π x))
    (t : NNReal) (f : γ → ℝ) (x : α) :
    finiteTimeExpectation M t (fun z => f (π z)) x=finiteTimeExpectation N t f (π x) := by
  obtain ⟨qN,hqN,_,hbN⟩ := N.exists_clock 0
  obtain ⟨q,hq,hqNq,hbM⟩ := M.exists_clock qN
  have hbN' (z : γ) : N.total z ≤ q := (hbN z).trans hqNq
  let P := M.uniformize q hq hbM
  let Q := N.uniformize q hq hbN'
  have hs (g : γ → ℝ) (z : α) : P.step (fun y => g (π y)) z=Q.step g (π z) := by
    simp only [P,Q,FiniteJumpModel.uniformize_step,hgen]
  have hn (n : Nat) (z : α) : P.steps n (fun y => f (π y)) z=Q.steps n f (π z) := by
    induction n generalizing z with
    | zero => rfl
    | succ n ih =>
      change P.step (P.steps n (fun y => f (π y))) z=Q.step (Q.steps n f) (π z)
      rw [show P.steps n (fun y => f (π y))=(fun y => Q.steps n f (π y)) from funext ih]
      exact hs _ z
  rw [finite_time_eq_uniformized M q t hq hbM,finite_time_eq_uniformized N q t hq hbN']
  unfold FiniteKernel.poissonized
  exact tsum_congr (fun n => congrArg (fun z => poissonWeight (q*t) n*z) (hn n x))

def quotaProject {σ : Type*} (J : Nat) (z : Option σ × Fin (J+1)) : Option (σ × Fin J) :=
  if hc : z.2.val < J then z.1.map (fun a => (a,⟨z.2.val,hc⟩)) else none

theorem quota_project_generator {σ β : Type*} [Fintype σ] [Fintype β] [DecidableEq σ]
    (M : FiniteJumpModel (Option σ) β) (J : Nat) (hdead : ∀ r, M.rate none r=0)
    (f : Option (σ × Fin J) → ℝ) (z : Option σ × Fin (J+1)) :
    (eventBudgetModel M J).generator (fun y => f (quotaProject J y)) z=
      (killedBudgetModel M J).generator f (quotaProject J z) := by
  rcases z with ⟨a,c⟩
  by_cases hc : c.val < J
  · cases a with
    | none => simp [FiniteJumpModel.generator,eventBudgetModel,hc,hdead,quotaProject,killedBudgetModel]
    | some a =>
      have he : min (c.val+1) J=c.val+1 := Nat.min_eq_left (by omega)
      have hn (r : β) : quotaProject J (M.next (some a) r,budgetIndex J c)=
          killedBudgetNext M J (some (a,⟨c.val,hc⟩)) r := by
        by_cases hh : c.val+1<J
        · simp [quotaProject,budgetIndex,he,killedBudgetNext,hh]
        · simp [quotaProject,budgetIndex,he,killedBudgetNext,hh]
      simp only [FiniteJumpModel.generator,eventBudgetModel,hc,if_true]
      simp only [quotaProject,hc,dif_pos,Option.map_some,killedBudgetModel,Option.elim]
      apply Finset.sum_congr rfl
      intro r _
      exact congrArg (fun v => M.rate (some a) r*(f v-f (some (a,⟨c.val,hc⟩)))) (hn r)
  · simp [FiniteJumpModel.generator,eventBudgetModel,hc,quotaProject,killedBudgetModel]

theorem killed_quota_deadline {σ β : Type*} [Fintype σ] [Fintype β] [DecidableEq σ]
    (M : FiniteJumpModel (Option σ) β) (h v w : Option σ → ℝ) (δ η s : ℝ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hs : 0 < s) (hdead : ∀ r, M.rate none r=0)
    (hh0 : h none=0) (hvu : ∀ x, v x ≤ 1) (hwn : ∀ x, 0 ≤ w x)
    (hrate : ∀ x, M.total x ≤ 4000000)
    (hv : ∀ x, -δ ≤ M.generator v x)
    (hw : ∀ x, M.generator w x ≤ -s*w x+η)
    (hcover : ∀ x, v x ≤ h x+w x) (x : σ) :
    v (some x)-20*δ-Real.exp (-s*20)*w (some x)-η/s-1/5000000 ≤
      finiteTimeExpectation (killedBudgetModel M 100000000) 20
        (killedBudgetObservable 100000000 h) (some (x,0)) := by
  have hh := event_quota_deadline M h v w δ η s hδ hη hs hvu hwn hrate hv hw hcover (some x)
  have he := finite_time_generator_map (eventBudgetModel M 100000000)
    (killedBudgetModel M 100000000) (quotaProject 100000000)
    (quota_project_generator M 100000000 hdead) 20 (killedBudgetObservable 100000000 h) (some x,0)
  have ho : (fun z => killedBudgetObservable 100000000 h (quotaProject 100000000 z))=
      budgetObservable 100000000 h := by
    funext z
    rcases z with ⟨a,c⟩
    by_cases hc : c.val < 100000000
    · cases a <;> simp [quotaProject,killedBudgetObservable,budgetObservable,hc,hh0]
    · simp [quotaProject,killedBudgetObservable,budgetObservable,hc]
  rw [ho] at he
  simpa [quotaProject] using hh.trans_eq he

end
end CompositionalMemory

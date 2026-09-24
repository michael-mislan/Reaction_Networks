import proofs.RandomViability.BindingCompetitionSupplyRates
import proofs.FiniteCopy.KernelExpectations

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

abbrev CompetitionGrossCounters (C : ℕ) := Fin 4 → Fin (C+1)

def competitionServiceLabel : CompetitionChannel → Option (Fin 4)
  | .inl j => if j=10 then some 0 else if j=11 then some 1 else none
  | .inr j => if j=0 then some 2 else some 3

def competitionCounterNext {C : ℕ} (c : CompetitionGrossCounters C)
    (label : Option (Fin 4)) : CompetitionGrossCounters C :=
  match label with
  | none => c
  | some j => fun i => if i=j then ⟨min C ((c i).val+1),by have := Nat.min_le_left C ((c i).val+1); omega⟩ else c i

/-- U feed, W feed, or the sum of the two separate driven gross counters. -/
def competitionServiceCount {C : ℕ} (mode : Fin 3) (c : CompetitionGrossCounters C) : ℕ :=
  if mode=0 then (c 0).val else if mode=1 then (c 1).val else (c 2).val+(c 3).val

def competitionServiceIncrement (mode : Fin 3) (label : Option (Fin 4)) : ℕ :=
  match label with
  | none => 0
  | some j => if mode=0 then (if j=0 then 1 else 0)
    else if mode=1 then (if j=1 then 1 else 0) else (if j=2 ∨ j=3 then 1 else 0)

theorem competition_counter_increment_bound {C : ℕ} (mode : Fin 3) (c : CompetitionGrossCounters C)
    (label : Option (Fin 4)) :
    competitionServiceCount mode (competitionCounterNext c label) ≤
      competitionServiceCount mode c+competitionServiceIncrement mode label := by
  cases label with
  | none => simp [competitionCounterNext,competitionServiceIncrement]
  | some j =>
    fin_cases mode <;> fin_cases j <;>
      norm_num [competitionServiceCount,competitionCounterNext,competitionServiceIncrement,Fin.ext_iff] <;> omega

theorem competition_service_increment_binary (mode : Fin 3) (label : Option (Fin 4)) :
    competitionServiceIncrement mode label=0 ∨ competitionServiceIncrement mode label=1 := by
  cases label with
  | none => exact Or.inl rfl
  | some j => fin_cases mode <;> fin_cases j <;> norm_num [competitionServiceIncrement,Fin.ext_iff]

section Model
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (C : ℕ) (M : FiniteJumpModel α β) (mark : β → Option (Fin 4))

def competitionCountedModel : FiniteJumpModel (α × CompetitionGrossCounters C) β where
  next X j := (M.next X.1 j,competitionCounterNext X.2 (mark j))
  rate X j := M.rate X.1 j
  nonneg X j := M.nonneg X.1 j

omit [DecidableEq α] in
theorem competition_counted_total (X : α × CompetitionGrossCounters C) :
    (competitionCountedModel C M mark).total X=M.total X.1 := rfl

omit [DecidableEq α] in
theorem competition_counted_generator (f : α → ℝ) (X : α × CompetitionGrossCounters C) :
    (competitionCountedModel C M mark).generator (fun Z => f Z.1) X=M.generator f X.1 := rfl

variable (q : ℝ) (hq : 0 < q) (hb : ∀ X, M.total X ≤ q)

theorem competition_counted_step (f : α → ℝ) (X : α × CompetitionGrossCounters C) :
    ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).step (fun Z => f Z.1) X=
      (M.uniformize q hq hb).step f X.1 := by
  rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step]
  rfl

theorem competition_counted_steps (n : ℕ) (f : α → ℝ) (X : α × CompetitionGrossCounters C) :
    ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).steps n (fun Z => f Z.1) X=
      (M.uniformize q hq hb).steps n f X.1 := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteKernel.steps]
    rw [show ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).steps n
      (fun Z => f Z.1) = (fun Z => (M.uniformize q hq hb).steps n f Z.1) from funext ih]
    exact competition_counted_step C M mark q hq hb _ X

theorem competition_counted_poisson (t : ℝ≥0) (f : α → ℝ) (X : α × CompetitionGrossCounters C) :
    ((competitionCountedModel C M mark).uniformize q hq (fun Z => hb Z.1)).poissonized t (fun Z => f Z.1) X=
      (M.uniformize q hq hb).poissonized t f X.1 := by
  unfold FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [competition_counted_steps]

end Model
end
end RandomViability.Binding

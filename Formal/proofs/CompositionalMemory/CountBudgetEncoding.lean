import proofs.CompositionalMemory.FiniteKilledEventBudget
import proofs.CompositionalMemory.FiniteEncoding

namespace CompositionalMemory
open FiniteCopy

def countBudgetNext {α β : Type*} (next : α → β → α) (J : Nat)
    (z : α × Nat) (r : β) : α × Nat :=
  if z.2<J then (next z.1 r,z.2+1) else z

def countBudgetEmbed {α σ : Type*} (embed : σ → α) (J : Nat) (z : σ × Fin J) : α × Nat :=
  (embed z.1,z.2.val)

def countBudgetClip {α σ : Type*} (clip : α → Option σ) (J : Nat) (z : α × Nat) :
    Option (σ × Fin J) :=
  if hc : z.2<J then (clip z.1).map (fun a => (a,⟨z.2,hc⟩)) else none

theorem countBudget_clip_embed {α σ : Type*} (embed : σ → α) (clip : α → Option σ)
    (hleft : ∀ a, clip (embed a)=some a) (J : Nat) (z : σ × Fin J) :
    countBudgetClip clip J (countBudgetEmbed embed J z)=some z := by
  rcases z with ⟨a,c⟩
  simp [countBudgetClip,countBudgetEmbed,c.isLt,hleft]

theorem countBudget_embed_clip {α σ : Type*} (embed : σ → α) (clip : α → Option σ)
    (hright : ∀ x a, clip x=some a → embed a=x) (J : Nat)
    (x : α × Nat) (z : σ × Fin J) (h : countBudgetClip clip J x=some z) :
    countBudgetEmbed embed J z=x := by
  rcases x with ⟨x,c⟩
  simp only [countBudgetClip] at h
  split_ifs at h with hc
  · cases hh : clip x with
    | none => simp [hh] at h
    | some a =>
      simp only [hh,Option.map_some,Option.some.injEq] at h
      rw [← h]
      simp [countBudgetEmbed,hright x a hh]

theorem countBudget_next_encoding {α σ β : Type*} [Fintype σ] [Fintype β]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (next : α → β → α) (rate : α → β → ℝ) (hr : ∀ x r, 0 ≤ rate x r)
    (embed : σ → α) (clip : α → Option σ) (J : Nat) (z : σ × Fin J) (r : β) :
    countBudgetClip clip J (countBudgetNext next J (countBudgetEmbed embed J z) r)=
      killedBudgetNext (encodedFiniteModel next rate hr embed clip) J (some z) r := by
  rcases z with ⟨a,c⟩
  simp [countBudgetNext,countBudgetEmbed,countBudgetClip,c.isLt,
    killedBudgetNext,encodedFiniteModel]

theorem countBudget_model_encoding {α σ β : Type*} [Fintype σ] [Fintype β]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (next : α → β → α) (rate : α → β → ℝ) (hr : ∀ x r, 0 ≤ rate x r)
    (embed : σ → α) (clip : α → Option σ) (J : Nat) :
    encodedFiniteModel (countBudgetNext next J) (fun z r => rate z.1 r) (fun z r => hr z.1 r)
      (countBudgetEmbed embed J) (countBudgetClip clip J)=
      killedBudgetModel (encodedFiniteModel next rate hr embed clip) J := by
  have heq (P Q : FiniteJumpModel (Option (σ × Fin J)) β)
      (hn : P.next=Q.next) (hrate : P.rate=Q.rate) : P=Q := by
    cases P
    cases Q
    cases hn
    cases hrate
    rfl
  apply heq
  · funext z r
    cases z with
    | none => rfl
    | some z => exact countBudget_next_encoding next rate hr embed clip J z r
  · funext z r
    cases z <;> rfl

end CompositionalMemory

import proofs.FiniteCopy.UniformizedBounds

namespace CompositionalMemory
open FiniteCopy

noncomputable def reactionGenerator {S R : Type*} [Fintype R]
    (next : S → R → S) (rate : S → R → ℝ) (f : S → ℝ) (s : S) : ℝ :=
  ∑ r, rate s r*(f (next s r)-f s)

/-- Literal reactions until either an unsafe departure or an inactive state.
Unsafe departure is absorbing; inactive states (such as division) are frozen. -/
noncomputable def retainedReactionModel {S R : Type*} [Fintype R]
    (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) : FiniteJumpModel (Option {s : S // s ∈ D}) R := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some s => if active s.val then
          if h : next s.val r ∈ D then some ⟨next s.val r,h⟩ else none
        else some s
    rate := fun s r => match s with
      | none => 0
      | some s => if active s.val then rate s.val r else 0
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some s =>
        change 0 ≤ if active s.val then rate s.val r else 0
        split_ifs
        · exact hrate s.val r
        · rfl }

noncomputable def retainedReactionObservable {S : Type*} (D : Finset S)
    (f : S → ℝ) (boundary : ℝ) : Option {s : S // s ∈ D} → ℝ
  | none => boundary
  | some s => f s.val

theorem retained_reaction_generator_le {S R : Type*} [Fintype R]
    (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) (f : S → ℝ) (boundary : ℝ)
    (hb : ∀ s ∈ D, active s → ∀ r, next s r ∉ D → boundary ≤ f (next s r))
    (s : {s : S // s ∈ D}) (hs : active s.val) :
    (retainedReactionModel next rate hrate active D).generator
      (retainedReactionObservable D f boundary) (some s) ≤ reactionGenerator next rate f s.val := by
  classical
  unfold FiniteJumpModel.generator reactionGenerator
  apply Finset.sum_le_sum
  intro r _
  have hh : retainedReactionObservable D f boundary
      ((retainedReactionModel next rate hrate active D).next (some s) r) ≤ f (next s.val r) := by
    by_cases hd : next s.val r ∈ D
    · simp [retainedReactionModel,retainedReactionObservable,hs,hd]
    · simpa [retainedReactionModel,retainedReactionObservable,hs,hd] using hb s.val s.property hs r hd
  simpa [retainedReactionModel,retainedReactionObservable,hs] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hh (f s.val)) (hrate s.val r)

theorem retained_reaction_event_bound {S R : Type*} [Fintype R] [DecidableEq S]
    (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) (f : S → ℝ) (boundary driftBound : ℝ)
    (hboundary : 0 ≤ boundary) (hB : 0 ≤ driftBound) (hf : ∀ s ∈ D, 0 ≤ f s)
    (hb : ∀ s ∈ D, active s → ∀ r, next s r ∉ D → boundary ≤ f (next s r))
    (hgen : ∀ s ∈ D, active s → reactionGenerator next rate f s ≤ driftBound)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate active D).total s ≤ q)
    (s : {s : S // s ∈ D}) :
    boundary*((retainedReactionModel next rate hrate active D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤ f s.val+(t : ℝ)*driftBound := by
  classical
  apply (retainedReactionModel next rate hrate active D).uniformized_event_bound q t hq hclock
    {none} (retainedReactionObservable D f boundary) boundary driftBound
  · intro x
    cases x with
    | none => exact hboundary
    | some x => exact hf x.val x.property
  · intro x hx
    have hx' : x=none := hx
    subst x
    exact le_rfl
  · intro x
    cases x with
    | none => simpa [retainedReactionModel,FiniteJumpModel.generator] using hB
    | some x =>
      by_cases hx : active x.val
      · exact (retained_reaction_generator_le next rate hrate active D f boundary hb x hx).trans
          (hgen x.val x.property hx)
      · simpa [retainedReactionModel,FiniteJumpModel.generator,hx] using hB

end CompositionalMemory

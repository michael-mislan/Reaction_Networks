import proofs.CompositionalMemory.ModularStopped
import proofs.CompositionalMemory.ProductDomain

namespace CompositionalMemory
open FiniteCopy

/-- Division states are retained and frozen. `none` records unsafe departure.
Choosing D to exclude division instead gives the killed pre-division model. -/
noncomputable def retainedModularModel {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (N : ℕ)
    (D : Finset (ModularCountState k)) : FiniteJumpModel (StoppedModularState D) (ModularChannel k) := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some s => if s.val.2 < 2*(k*N) then
          if h : modularNext s.val r ∈ D then some ⟨modularNext s.val r,h⟩ else none
        else some s
    rate := fun s r => match s with
      | none => 0
      | some s => if s.val.2 < 2*(k*N) then modularRate γ w s.val r else 0
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some s =>
        change 0 ≤ if s.val.2 < 2*(k*N) then modularRate γ w s.val r else 0
        split_ifs
        · exact modular_rate_nonnegative γ w hγ hw s.val r
        · rfl }

noncomputable def retainedModularObservable (D : Finset (ModularCountState k)) (f : ModularCountState k → ℝ)
    (boundary : ℝ) : StoppedModularState D → ℝ
  | none => boundary
  | some s => f s.val

theorem retained_modular_generator_le {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (N : ℕ)
    (D : Finset (ModularCountState k)) (f : ModularCountState k → ℝ) (boundary : ℝ)
    (hb : ∀ s ∈ D, s.2 < 2*(k*N) → ∀ r, modularNext s r ∉ D → boundary ≤ f (modularNext s r))
    (s : {s : ModularCountState k // s ∈ D}) (hs : s.val.2 < 2*(k*N)) :
    (retainedModularModel γ w hγ hw N D).generator (retainedModularObservable D f boundary) (some s) ≤
      modularGenerator γ w f s.val := by
  classical
  unfold FiniteJumpModel.generator modularGenerator
  apply Finset.sum_le_sum
  intro r _
  have hh : retainedModularObservable D f boundary ((retainedModularModel γ w hγ hw N D).next (some s) r) ≤
      f (modularNext s.val r) := by
    by_cases hd : modularNext s.val r ∈ D
    · simp [retainedModularModel,retainedModularObservable,hs,hd]
    · simpa [retainedModularModel,retainedModularObservable,hs,hd] using hb s.val s.property hs r hd
  simpa [retainedModularModel,retainedModularObservable,hs] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hh (f s.val)) (modular_rate_nonnegative γ w hγ hw s.val r)

theorem retained_modular_event_bound {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (N : ℕ)
    (D : Finset (ModularCountState k)) (f : ModularCountState k → ℝ) (boundary driftBound : ℝ)
    (hboundary : 0 ≤ boundary) (hB : 0 ≤ driftBound)
    (hf : ∀ s ∈ D, 0 ≤ f s)
    (hb : ∀ s ∈ D, s.2 < 2*(k*N) → ∀ r, modularNext s r ∉ D → boundary ≤ f (modularNext s r))
    (hgen : ∀ s ∈ D, s.2 < 2*(k*N) → modularGenerator γ w f s ≤ driftBound)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedModularModel γ w hγ hw N D).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ D}) :
    boundary*((retainedModularModel γ w hγ hw N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤ f s.val+(t : ℝ)*driftBound := by
  classical
  apply (retainedModularModel γ w hγ hw N D).uniformized_event_bound q t hq hclock
    {none} (retainedModularObservable D f boundary) boundary driftBound
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
    | none => simpa [retainedModularModel,FiniteJumpModel.generator] using hB
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N)
      · exact (retained_modular_generator_le γ w hγ hw N D f boundary hb x hx).trans
          (hgen x.val x.property hx)
      · simpa [retainedModularModel,FiniteJumpModel.generator,hx] using hB

end CompositionalMemory

import proofs.HeritableCompositions.Source
import proofs.FiniteCopy.UniformizedBounds

namespace HeritableCompositions
open FiniteCopy

noncomputable def compartmentGenerator (γ : ℝ) (f : Compartment → ℝ)
    (s : Compartment) : ℝ :=
  ∑ r : Channel, propensity γ s r*(f (nextCompartment s r)-f s)

abbrev StoppedCompartment (D : Finset Compartment) := Option {s : Compartment // s ∈ D}

/-- Division states are retained and frozen. `none` records unsafe departure.
Choosing D to exclude division instead gives the killed pre-division model. -/
noncomputable def stoppedGrowthModel (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ)
    (D : Finset Compartment) : FiniteJumpModel (StoppedCompartment D) Channel := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some s => if s.val.2 < 2*N then
          if h : nextCompartment s.val r ∈ D then some ⟨nextCompartment s.val r,h⟩ else none
        else some s
    rate := fun s r => match s with
      | none => 0
      | some s => if s.val.2 < 2*N then propensity γ s.val r else 0
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some s =>
        change 0 ≤ if s.val.2 < 2*N then propensity γ s.val r else 0
        split_ifs
        · exact propensity_nonneg γ hγ s.val r
        · rfl }

noncomputable def growthObservable (D : Finset Compartment) (f : Compartment → ℝ)
    (boundary : ℝ) : StoppedCompartment D → ℝ
  | none => boundary
  | some s => f s.val

theorem stopped_growth_generator_le (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ)
    (D : Finset Compartment) (f : Compartment → ℝ) (boundary : ℝ)
    (hb : ∀ s ∈ D, s.2 < 2*N → ∀ r, nextCompartment s r ∉ D → boundary ≤ f (nextCompartment s r))
    (s : {s : Compartment // s ∈ D}) (hs : s.val.2 < 2*N) :
    (stoppedGrowthModel γ hγ N D).generator (growthObservable D f boundary) (some s) ≤
      compartmentGenerator γ f s.val := by
  classical
  unfold FiniteJumpModel.generator compartmentGenerator
  apply Finset.sum_le_sum
  intro r _
  have hh : growthObservable D f boundary ((stoppedGrowthModel γ hγ N D).next (some s) r) ≤
      f (nextCompartment s.val r) := by
    by_cases hd : nextCompartment s.val r ∈ D
    · simp [stoppedGrowthModel,growthObservable,hs,hd]
    · simpa [stoppedGrowthModel,growthObservable,hs,hd] using hb s.val s.property hs r hd
  simpa [stoppedGrowthModel,growthObservable,hs] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hh (f s.val)) (propensity_nonneg γ hγ s.val r)

theorem stopped_growth_event_bound (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ)
    (D : Finset Compartment) (f : Compartment → ℝ) (boundary driftBound : ℝ)
    (hboundary : 0 ≤ boundary) (hB : 0 ≤ driftBound)
    (hf : ∀ s ∈ D, 0 ≤ f s)
    (hb : ∀ s ∈ D, s.2 < 2*N → ∀ r, nextCompartment s r ∉ D → boundary ≤ f (nextCompartment s r))
    (hgen : ∀ s ∈ D, s.2 < 2*N → compartmentGenerator γ f s ≤ driftBound)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (stoppedGrowthModel γ hγ N D).total s ≤ q)
    (s : {s : Compartment // s ∈ D}) :
    boundary*((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤ f s.val+(t : ℝ)*driftBound := by
  classical
  apply (stoppedGrowthModel γ hγ N D).uniformized_event_bound q t hq hclock
    {none} (growthObservable D f boundary) boundary driftBound
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
    | none => simpa [stoppedGrowthModel,FiniteJumpModel.generator] using hB
    | some x =>
      by_cases hx : x.val.2 < 2*N
      · exact (stopped_growth_generator_le γ hγ N D f boundary hb x hx).trans
          (hgen x.val x.property hx)
      · simpa [stoppedGrowthModel,FiniteJumpModel.generator,hx] using hB

end HeritableCompositions

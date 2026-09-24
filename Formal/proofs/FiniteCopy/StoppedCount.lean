import proofs.FiniteCopy.CountSource
import proofs.FiniteCopy.ExponentialFoster
import proofs.FiniteCopy.UniformizedBounds

namespace FiniteCopy
open scoped NNReal

abbrev StoppedCounts (D : Finset Counts) := Option {n : Counts // n ∈ D}

/-- Literal count reactions until departure from a finite domain. The extra
state is absorbing; an impossible reaction has rate zero by CountSource. -/
noncomputable def stoppedCountModel (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts) :
    FiniteJumpModel (StoppedCounts D) (Fin 13) := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some n => if h : nextCounts n.val r ∈ D then some ⟨nextCounts n.val r,h⟩ else none
    rate := fun s r => match s with
      | none => 0
      | some n => (N : ℝ)*densityRates e (1/(N : ℝ)) (concentration N n.val) r
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some n => exact mul_nonneg (Nat.cast_nonneg N) (lattice_rates_nonneg e he N n.val r) }

noncomputable def stoppedObservable (N : ℕ) (D : Finset Counts) (f : Point → ℝ) (a : ℝ) :
    StoppedCounts D → ℝ
  | none => a
  | some n => f (concentration N n.val)

theorem stopped_none_generator (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : StoppedCounts D → ℝ) : (stoppedCountModel e he N D).generator f none = 0 := by
  simp [stoppedCountModel, FiniteJumpModel.generator]

theorem stopped_generator_le (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a : ℝ)
    (hboundary : ∀ n ∈ D, ∀ r, reactants n r → nextCounts n r ∉ D →
      a ≤ f (concentration N (nextCounts n r))) (n : {n : Counts // n ∈ D}) :
    (stoppedCountModel e he N D).generator (stoppedObservable N D f a) (some n) ≤
      generator e N f (concentration N n.val) := by
  classical
  unfold FiniteJumpModel.generator generator
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : reactants n.val r
  · have hnext : stoppedObservable N D f a ((stoppedCountModel e he N D).next (some n) r) ≤
        f (fun i => concentration N n.val i+jump r i/(N : ℝ)) := by
      rw [← concentration_next N n.val r hr]
      by_cases hd : nextCounts n.val r ∈ D
      · simp [stoppedObservable, stoppedCountModel, hd]
      · simpa [stoppedObservable, stoppedCountModel, hd] using hboundary n.val n.property r hr hd
    have hrate := mul_nonneg (Nat.cast_nonneg N) (lattice_rates_nonneg e he N n.val r)
    have hh := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hnext (f (concentration N n.val))) hrate
    simpa [stoppedObservable, stoppedCountModel, mul_assoc] using hh
  · have hz := disabled_density_zero e N n.val r hr
    simp only [one_div] at hz
    simp [stoppedCountModel, hz]

theorem stopped_generator_bound (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a b : ℝ) (hb : 0 ≤ b)
    (hboundary : ∀ n ∈ D, ∀ r, reactants n r → nextCounts n r ∉ D →
      a ≤ f (concentration N (nextCounts n r)))
    (hgen : ∀ n ∈ D, generator e N f (concentration N n) ≤ b) (s : StoppedCounts D) :
    (stoppedCountModel e he N D).generator (stoppedObservable N D f a) s ≤ b := by
  cases s with
  | none => simpa only [stopped_none_generator] using hb
  | some n => exact (stopped_generator_le e he N D f a hboundary n).trans (hgen n.val n.property)

/-- Direct source-level event estimate. Its remaining hypotheses are pointwise
source inequalities, not a stochastic theorem supplied as a premise. -/
theorem stopped_source_event_bound (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n ∈ D, 0 ≤ f (concentration N n))
    (hboundary : ∀ n ∈ D, ∀ r, reactants n r → nextCounts n r ∉ D →
      a ≤ f (concentration N (nextCounts n r)))
    (hgen : ∀ n ∈ D, generator e N f (concentration N n) ≤ b)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (stoppedCountModel e he N D).total s ≤ q)
    (n : {n : Counts // n ∈ D}) :
    a*((stoppedCountModel e he N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some n) ≤ f (concentration N n.val)+(t : ℝ)*b := by
  classical
  apply (stoppedCountModel e he N D).uniformized_event_bound q t hq hclock
    {none} (stoppedObservable N D f a) a b
  · intro s
    cases s with
    | none => exact ha
    | some m => exact hf m.val m.property
  · intro s hs
    have hs' : s=none := hs
    subst s
    exact le_rfl
  · exact stopped_generator_bound e he N D f a b hb hboundary hgen

end FiniteCopy

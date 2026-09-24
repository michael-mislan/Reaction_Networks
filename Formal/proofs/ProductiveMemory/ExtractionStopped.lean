import proofs.ProductiveMemory.ExtractionCountSource
import proofs.ProductiveMemory.ExtractionGenerator
import proofs.FiniteCopy.StoppedCount

namespace ProductiveMemory
open FiniteCopy
set_option Elab.async false
open scoped NNReal

abbrev ExtractionStoppedCounts (D : Finset Counts) := Option {n : Counts // n ∈ D}

/-- Literal count reactions until departure from a finite domain. The extra
state is absorbing; an impossible reaction has rate zero by CountSource. -/
noncomputable def extractionStoppedModel (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts) :
    FiniteJumpModel (ExtractionStoppedCounts D) (ExtractionChannel) := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some n => if h : channelNext n.val r ∈ D then some ⟨channelNext n.val r,h⟩ else none
    rate := fun s r => match s with
      | none => 0
      | some n => (N : ℝ)*channelDensity e (1/(N : ℝ)) (concentration N n.val) r
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some n => exact mul_nonneg (Nat.cast_nonneg N) (extraction_rate_nonneg e he N n.val r) }

noncomputable def extractionStoppedObservable (N : ℕ) (D : Finset Counts) (f : Point → ℝ) (a : ℝ) :
    ExtractionStoppedCounts D → ℝ
  | none => a
  | some n => f (concentration N n.val)

theorem extraction_stopped_none_generator (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : ExtractionStoppedCounts D → ℝ) : (extractionStoppedModel e he N D).generator f none = 0 := by
  simp [extractionStoppedModel, FiniteJumpModel.generator]

theorem extraction_stopped_generator_le (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a : ℝ)
    (hboundary : ∀ n ∈ D, ∀ r, channelEnabled n r → channelNext n r ∉ D →
      a ≤ f (concentration N (channelNext n r))) (n : {n : Counts // n ∈ D}) :
    (extractionStoppedModel e he N D).generator (extractionStoppedObservable N D f a) (some n) ≤
      countGenerator e N f (concentration N n.val) := by
  classical
  unfold FiniteJumpModel.generator countGenerator
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  by_cases hr : channelEnabled n.val r
  · have hnext : extractionStoppedObservable N D f a ((extractionStoppedModel e he N D).next (some n) r) ≤
        f (fun i => concentration N n.val i+channelJump r i/(N : ℝ)) := by
      rw [← channel_concentration_next N n.val r hr]
      by_cases hd : channelNext n.val r ∈ D
      · simp [extractionStoppedObservable, extractionStoppedModel, hd]
      · simpa [extractionStoppedObservable, extractionStoppedModel, hd] using hboundary n.val n.property r hr hd
    have hrate := mul_nonneg (Nat.cast_nonneg N) (extraction_rate_nonneg e he N n.val r)
    have hh := mul_le_mul_of_nonneg_left
      (sub_le_sub_right hnext (f (concentration N n.val))) hrate
    simpa [extractionStoppedObservable, extractionStoppedModel, mul_assoc] using hh
  · have hz := channel_disabled_zero e N n.val r hr
    simp only [one_div] at hz
    simp [extractionStoppedModel, hz]

theorem extraction_stopped_generator_bound (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a b : ℝ) (hb : 0 ≤ b)
    (hboundary : ∀ n ∈ D, ∀ r, channelEnabled n r → channelNext n r ∉ D →
      a ≤ f (concentration N (channelNext n r)))
    (hgen : ∀ n ∈ D, countGenerator e N f (concentration N n) ≤ b) (s : ExtractionStoppedCounts D) :
    (extractionStoppedModel e he N D).generator (extractionStoppedObservable N D f a) s ≤ b := by
  cases s with
  | none => simpa only [extraction_stopped_none_generator] using hb
  | some n => exact (extraction_stopped_generator_le e he N D f a hboundary n).trans (hgen n.val n.property)

/-- Direct source-level event estimate. Its remaining hypotheses are pointwise
source inequalities, not a stochastic theorem supplied as a premise. -/
theorem extraction_stopped_source_event_bound (e : ℝ) (he : 0 ≤ e) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n ∈ D, 0 ≤ f (concentration N n))
    (hboundary : ∀ n ∈ D, ∀ r, channelEnabled n r → channelNext n r ∉ D →
      a ≤ f (concentration N (channelNext n r)))
    (hgen : ∀ n ∈ D, countGenerator e N f (concentration N n) ≤ b)
    (q t : ℝ≥0) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (extractionStoppedModel e he N D).total s ≤ q)
    (n : {n : Counts // n ∈ D}) :
    a*((extractionStoppedModel e he N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some n) ≤ f (concentration N n.val)+(t : ℝ)*b := by
  classical
  apply (extractionStoppedModel e he N D).uniformized_event_bound q t hq hclock
    {none} (extractionStoppedObservable N D f a) a b
  · intro s
    cases s with
    | none => exact ha
    | some m => exact hf m.val m.property
  · intro s hs
    have hs' : s=none := hs
    subst s
    exact le_rfl
  · exact extraction_stopped_generator_bound e he N D f a b hb hboundary hgen

end ProductiveMemory

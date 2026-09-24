import proofs.SparseLinearRAF.LiteratureResolution
import proofs.SparseLinearRAF.SelfConstructionLimit

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory Filter Topology

/-- Minimum over a natural-valued predicate, with infinity when it is empty. -/
noncomputable def minimumOrInfinity (P : Nat → Prop) : WithTop Nat := by
  classical
  exact if h : ∃ m, P m then WithTop.some (Nat.find h) else ⊤

theorem minimumOrInfinity_le_iff (P : Nat → Prop) (N : Nat) :
    minimumOrInfinity P ≤ WithTop.some N ↔ ∃ m, P m ∧ m ≤ N := by
  classical
  unfold minimumOrInfinity
  split_ifs with h
  · simp only [WithTop.coe_le_coe]
    constructor
    · intro hn
      exact ⟨Nat.find h, Nat.find_spec h, hn⟩
    · rintro ⟨m, hm, hn⟩
      exact (Nat.find_min' h hm).trans hn
  · simp only [WithTop.top_le_iff, WithTop.coe_ne_top, false_iff]
    rintro ⟨m, hm, _⟩
    exact h ⟨m, hm⟩

noncomputable def minimumRAFSize (n t : Nat)
    (ω : SparseSample (Molecule n) (Reaction n)) : WithTop Nat :=
  minimumOrInfinity (fun m => ∃ T : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n t) (sparseCatalysis ω) T ∧ T.card = m)

theorem minimumRAFSize_le_iff (n t N : Nat)
    (ω : SparseSample (Molecule n) (Reaction n)) :
    minimumRAFSize n t ω ≤ WithTop.some N ↔
      ∃ T : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n t) (sparseCatalysis ω) T ∧ T.card ≤ N := by
  rw [minimumRAFSize, minimumOrInfinity_le_iff]
  constructor
  · rintro ⟨m, ⟨T, hT, rfl⟩, hm⟩
    exact ⟨T, hT, hm⟩
  · rintro ⟨T, hT, hm⟩
    exact ⟨T.card, ⟨T, hT, rfl⟩, hm⟩

theorem minimum_raf_size_superlinear (t C : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => (sparseMeasure (Molecule n) (Reaction n)
      (activityParameter n lambda) (channelParameter n)
      {ω | minimumRAFSize n t ω ≤ WithTop.some (C*n)}).toReal) atTop (𝓝 0) := by
  simpa only [minimumRAFSize_le_iff, linearRAFProbability, HasLinearRAF] using
    sparse_linear_raf_probability_tendsto_zero t C hl

/-- The minimum size of an active, internally reachable catalyst cover of a RAF. -/
noncomputable def minimumCatalystRank (n t : Nat)
    (ω : SparseSample (Molecule n) (Reaction n)) : WithTop Nat :=
  minimumOrInfinity (fun k => 0 < k ∧ HasCoverRank n t k ω)

theorem minimumCatalystRank_le_iff (n t K : Nat)
    (ω : SparseSample (Molecule n) (Reaction n)) :
    minimumCatalystRank n t ω ≤ WithTop.some K ↔ HasBoundedCoverRank n t K ω := by
  rw [minimumCatalystRank, minimumOrInfinity_le_iff]
  unfold HasBoundedCoverRank
  aesop

theorem minimum_catalyst_rank_diverges (t K : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => (sparseMeasure (Molecule n) (Reaction n)
      (activityParameter n lambda) (channelParameter n)
      {ω | minimumCatalystRank n t ω ≤ WithTop.some K}).toReal) atTop (𝓝 0) := by
  simpa only [minimumCatalystRank_le_iff, boundedCoverRankProbability] using
    bounded_cover_rank_probability_tendsto_zero t K hl

/-- For a subevent, conditional probability is its probability divided by that
of the conditioning event. An eventual positive denominator is sufficient. -/
theorem conditional_probability_vanishes {p q : Nat → ℝ} {delta : ℝ}
    (hp : ∀ n, 0 ≤ p n) (ht : Tendsto p atTop (𝓝 0)) (hd : 0 < delta)
    (hq : ∀ᶠ n in atTop, delta ≤ q n) :
    Tendsto (fun n => p n / q n) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (by simpa using ht.div_const delta)
  · filter_upwards [hq] with n hn
    exact div_nonneg (hp n) (hd.le.trans hn)
  · filter_upwards [hq] with n hn
    exact div_le_div_of_nonneg_left (hp n) hd hn

theorem linear_raf_conditional_vanishes (t : Nat) (C : ℝ) {lambda delta : ℝ}
    (hl : 0 ≤ lambda) (hd : 0 < delta) (q : Nat → ℝ)
    (hq : ∀ᶠ n in atTop, delta ≤ q n) :
    Tendsto (fun n => literatureRAFProbability n t lambda C / q n) atTop (𝓝 0) :=
  conditional_probability_vanishes (fun _ => ENNReal.toReal_nonneg)
    (sparse_linear_raf_literature_resolution t C hl) hd hq

theorem bounded_rank_conditional_vanishes (t K : Nat) {lambda delta : ℝ}
    (hl : 0 ≤ lambda) (hd : 0 < delta) (q : Nat → ℝ)
    (hq : ∀ᶠ n in atTop, delta ≤ q n) :
    Tendsto (fun n => boundedCoverRankProbability n t K lambda / q n) atTop (𝓝 0) :=
  conditional_probability_vanishes (fun _ => ENNReal.toReal_nonneg)
    (bounded_cover_rank_probability_tendsto_zero t K hl) hd hq

/-- Scalar form of the window union bound; the literature supplies the upper
event estimate, while the formal root supplies the vanishing lower event. -/
theorem size_window_lower_bound {lower upper window error : Nat → ℝ} {epsilon : ℝ}
    (hupper : ∀ᶠ n in atTop, 1-epsilon-error n ≤ upper n)
    (hwindow : ∀ n, upper n-lower n ≤ window n)
    (hlower : Tendsto lower atTop (𝓝 0)) (herror : Tendsto error atTop (𝓝 0)) :
    ∃ remainder : Nat → ℝ, Tendsto remainder atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, 1-epsilon-remainder n ≤ window n := by
  refine ⟨fun n => error n+lower n, by simpa using herror.add hlower, ?_⟩
  filter_upwards [hupper] with n hn
  have hw := hwindow n
  linarith

end SparseLinearRAF

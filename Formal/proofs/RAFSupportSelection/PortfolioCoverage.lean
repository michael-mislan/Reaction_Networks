import Mathlib

namespace RAFSupportSelection

variable {I X : Type*} [DecidableEq I] [DecidableEq X]

def coverage (cover : I → Finset X) (P : Finset I) : Finset X := P.biUnion cover

def marginal (cover : I → Finset X) (P : Finset I) (i : I) : ℕ :=
  (cover i \ coverage cover P).card

omit [DecidableEq I] in
theorem coverage_mono (cover : I → Finset X) {P Q : Finset I} (h : P ⊆ Q) :
    coverage cover P ⊆ coverage cover Q := by
  intro x hx
  obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨i, h hi, hx⟩

/- Diminishing returns holds for the portfolio rescue objective. -/
omit [DecidableEq I] in
theorem marginal_antitone (cover : I → Finset X) {P Q : Finset I} (h : P ⊆ Q) (i : I) :
    marginal cover Q i ≤ marginal cover P i := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxi, hxQ⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨hxi, fun hp => hxQ (coverage_mono cover h hp)⟩

theorem coverage_insert (cover : I → Finset X) (P : Finset I) (i : I) :
    (coverage cover (insert i P)).card = (coverage cover P).card + marginal cover P i := by
  simp only [coverage, Finset.biUnion_insert, marginal]
  have he : cover i ∪ P.biUnion cover = (P.biUnion cover) ∪ (cover i \ P.biUnion cover) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [he, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp hy).2 hx)

/- Every size-b comparison portfolio is bounded by present coverage plus b times
the best available marginal. This supplies the actual greedy recurrence. -/
omit [DecidableEq I] in
theorem coverage_gap_bound (cover : I → Finset X) (P B : Finset I) (b g : ℕ)
    (hb : B.card ≤ b) (hg : ∀ i ∈ B, marginal cover P i ≤ g) :
    (coverage cover B).card ≤ (coverage cover P).card + b * g := by
  have hsub : coverage cover B ⊆ coverage cover P ∪
      B.biUnion (fun i => cover i \ coverage cover P) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    by_cases hp : x ∈ coverage cover P
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨i, hi, Finset.mem_sdiff.mpr ⟨hxi, hp⟩⟩)
  have hu := Finset.card_biUnion_le_card_mul B (fun i => cover i \ coverage cover P) g hg
  calc
    (coverage cover B).card ≤ (coverage cover P ∪ B.biUnion
        (fun i => cover i \ coverage cover P)).card := Finset.card_le_card hsub
    _ ≤ (coverage cover P).card +
        (B.biUnion (fun i => cover i \ coverage cover P)).card := Finset.card_union_le _ _
    _ ≤ (coverage cover P).card + b * g := Nat.add_le_add_left (hu.trans (Nat.mul_le_mul_right g hb)) _

/-- Finite-step greedy coverage guarantee. Using the gap bound above at each step
gives at least (1-(1-1/b)^k) of any size-b comparison portfolio's coverage. -/
theorem greedy_geometric_bound (f : ℕ → ℝ) (opt b : ℝ) (hb : 1 ≤ b)
    (hf : 0 ≤ f 0)
    (step : ∀ k, opt ≤ f k + b * (f (k+1) - f k)) (k : ℕ) :
    opt * (1 - (1 - 1/b)^k) ≤ f k := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have ha : 0 ≤ 1 - 1/b := by
    have hh : 1/b ≤ (1:ℝ) := (div_le_one hbpos).mpr hb
    linarith
  have hrec : ∀ j, opt - f (j+1) ≤ (1 - 1/b) * (opt - f j) := by
    intro j
    have hs := step j
    apply (mul_le_mul_iff_right₀ hbpos).mp
    field_simp
    nlinarith
  have hg : ∀ j, opt - f j ≤ (1 - 1/b)^j * opt := by
    intro j
    induction j with
    | zero => simp only [pow_zero, one_mul]; linarith
    | succ j ih =>
      calc
        opt - f (j+1) ≤ (1 - 1/b) * (opt - f j) := hrec j
        _ ≤ (1 - 1/b) * ((1 - 1/b)^j * opt) := mul_le_mul_of_nonneg_left ih ha
        _ = (1 - 1/b)^(j+1) * opt := by ring
  have hh := hg k
  nlinarith

section Algorithm
variable [LinearOrder I]

def pickMax (g : I → ℕ) (H : Finset I) (hH : H.Nonempty) : I :=
  (H.filter (fun i => g i = (H.image g).max' (hH.image g))).min' (by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (Finset.max'_mem (H.image g) (hH.image g))
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩)

omit [DecidableEq I] in
theorem pickMax_mem (g : I → ℕ) (H : Finset I) (hH : H.Nonempty) :
    pickMax g H hH ∈ H := by
  unfold pickMax
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).1

omit [DecidableEq I] in
theorem pickMax_ge (g : I → ℕ) (H : Finset I) (hH : H.Nonempty) (i : I) (hi : i ∈ H) :
    g i ≤ g (pickMax g H hH) := by
  have he : g (pickMax g H hH) = (H.image g).max' (hH.image g) := by
    unfold pickMax
    exact (Finset.mem_filter.mp (Finset.min'_mem
      (H.filter (fun i => g i = (H.image g).max' (hH.image g))) _)).2
  rw [he]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

def greedyPortfolio (cover : I → Finset X) (H : Finset I) (hH : H.Nonempty) : ℕ → Finset I
  | 0 => ∅
  | k+1 => let P := greedyPortfolio cover H hH k
      insert (pickMax (marginal cover P) H hH) P

theorem greedyPortfolio_subset (cover : I → Finset X) (H : Finset I) (hH : H.Nonempty) (k : ℕ) :
    greedyPortfolio cover H hH k ⊆ H := by
  induction k with
  | zero => simp [greedyPortfolio]
  | succ k ih =>
    exact Finset.insert_subset (pickMax_mem _ H hH) ih

theorem greedyPortfolio_card (cover : I → Finset X) (H : Finset I) (hH : H.Nonempty) (k : ℕ) :
    (greedyPortfolio cover H hH k).card ≤ k := by
  induction k with
  | zero => simp [greedyPortfolio]
  | succ k ih =>
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)

/-- Guarantee for the executable maximum-marginal portfolio, not for an assumed
optimal selector. The comparison is within the supplied finite candidate pool. -/
theorem greedyPortfolio_guarantee (cover : I → Finset X) (H : Finset I) (hH : H.Nonempty)
    (B : Finset I) (hBH : B ⊆ H) (b : ℕ) (hb : 1 ≤ b) (hB : B.card ≤ b) (k : ℕ) :
    ((coverage cover B).card : ℝ) * (1 - (1 - 1/(b:ℝ))^k) ≤
      (coverage cover (greedyPortfolio cover H hH k)).card := by
  apply greedy_geometric_bound
  · exact_mod_cast hb
  · simp [greedyPortfolio, coverage]
  · intro j
    let P := greedyPortfolio cover H hH j
    let i := pickMax (marginal cover P) H hH
    have hg := coverage_gap_bound cover P B b (marginal cover P i) hB
      (fun t ht => pickMax_ge _ H hH t (hBH ht))
    have hn := coverage_insert cover P i
    have hgR : ((coverage cover B).card : ℝ) ≤ (coverage cover P).card +
        (b:ℝ) * (marginal cover P i : ℝ) := by exact_mod_cast hg
    have hnR : ((coverage cover (insert i P)).card : ℝ) =
        (coverage cover P).card + (marginal cover P i : ℝ) := by exact_mod_cast hn
    change ((coverage cover B).card : ℝ) ≤ (coverage cover P).card +
      (b:ℝ) * (((coverage cover (insert i P)).card : ℝ) - (coverage cover P).card)
    rw [hnR]
    simpa only [add_sub_cancel_left] using hgR

end Algorithm

end RAFSupportSelection

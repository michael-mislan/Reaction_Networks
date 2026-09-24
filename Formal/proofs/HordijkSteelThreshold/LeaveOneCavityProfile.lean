import proofs.HordijkSteelThreshold.CavityWidthProbability

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- The loss caused by additionally withholding `x` from a `T`-closed sample
is exactly the singleton cavity width of the already `T`-closed system. -/
theorem rightTargetCavityWidth_preclosed_singleton_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    rightTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) {x} P k =
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2 \
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ {x})) P k).2 := by
  rw [rightTargetCavityWidth, closeTargetBlocks_union]

theorem leftTargetCavityWidth_preclosed_singleton_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    leftTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) {x} P k =
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1 \
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ {x})) P k).1 := by
  rw [leftTargetCavityWidth, closeTargetBlocks_union]

/-- Arbitrary held-block form of the pre-closed right cavity identity. -/
theorem rightTargetCavityWidth_preclosed_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    rightTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) U P k =
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2 \
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2 := by
  rw [rightTargetCavityWidth, closeTargetBlocks_union]

/-- Arbitrary held-block form of the pre-closed left cavity identity. -/
theorem leftTargetCavityWidth_preclosed_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    leftTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) U P k =
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1 \
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).1 := by
  rw [leftTargetCavityWidth, closeTargetBlocks_union]

/-- A pool gap caused by closing an arbitrary target block is contained in
the corresponding terminal right cavity width. -/
theorem card_rightTargetCavityWidth_preclosed_gt_sub
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hdeep :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).2.card < b) :
    B - b < (rightTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) U P k).card := by
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ U) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  rw [rightTargetCavityWidth_preclosed_eq,
    Finset.card_sdiff_of_subset hsub.2]
  omega

/-- Left-pool arbitrary-block mass-gap identity. -/
theorem card_leftTargetCavityWidth_preclosed_gt_sub
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hdeep :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).1.card < b) :
    B - b < (leftTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) U P k).card := by
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ U) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  rw [leftTargetCavityWidth_preclosed_eq,
    Finset.card_sdiff_of_subset hsub.1]
  omega

/-- If the base cavity has the required right-pool mass but withholding one
more target drops below the leave-one floor, the corresponding singleton
cavity width already exceeds the precise mass gap. -/
theorem card_rightTargetCavityWidth_preclosed_singleton_gt_sub
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).2.card < b) :
    B - b < (rightTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) {x} P k).card := by
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ {x}) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  rw [rightTargetCavityWidth_preclosed_singleton_eq,
    Finset.card_sdiff_of_subset hsub.2]
  omega

/-- Left-pool form of the exact low-mass exceptional-state reduction. -/
theorem card_leftTargetCavityWidth_preclosed_singleton_gt_sub
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).1.card < b) :
    B - b < (leftTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) {x} P k).card := by
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ {x}) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  rw [leftTargetCavityWidth_preclosed_singleton_eq,
    Finset.card_sdiff_of_subset hsub.1]
  omega

/-- Every discrepancy present at depth `k` is either an originally held
target or appeared in one of the first `k` fresh right generations.  This
does not assume that cavity widths are monotone in time. -/
theorem rightTargetCavityWidth_subset_held_union_fresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    rightTargetCavityWidth (foodLength := foodLength) Cat T P k ⊆
      T ∪ (Finset.range k).biUnion
        (freshRightTargetCavityWidth (foodLength := foodLength) Cat T P) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      by_cases hprev : x ∈ rightTargetCavityWidth
          (foodLength := foodLength) Cat T P k ∪ T
      · rcases Finset.mem_union.mp hprev with hxold | hxT
        · have hxcover := ih hxold
          rcases Finset.mem_union.mp hxcover with hxT | hxgen
          · exact Finset.mem_union_left _ hxT
          · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxgen
            exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr
                ⟨j, Finset.mem_range.mpr (by
                  have := Finset.mem_range.mp hj
                  omega), hxj⟩)
        · exact Finset.mem_union_left _ hxT
      · have hxfresh : x ∈ freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P k :=
          Finset.mem_sdiff.mpr ⟨hx, hprev⟩
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hxfresh⟩)

/-- Left-pool version of the finite fresh-generation cover. -/
theorem leftTargetCavityWidth_subset_held_union_fresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    leftTargetCavityWidth (foodLength := foodLength) Cat T P k ⊆
      T ∪ (Finset.range k).biUnion
        (freshLeftTargetCavityWidth (foodLength := foodLength) Cat T P) := by
  have hfun : freshRightTargetCavityWidth (foodLength := foodLength)
      Cat T (P.2, P.1) = freshLeftTargetCavityWidth
        (foodLength := foodLength) Cat T P := by
    funext j
    simp only [freshRightTargetCavityWidth_eq_left_swap, Prod.eta]
  rw [← hfun]
  simpa only [rightTargetCavityWidth_eq_left_swap, Prod.fst, Prod.snd,
    Prod.eta] using
    (rightTargetCavityWidth_subset_held_union_fresh
      (foodLength := foodLength) Cat T (P.2, P.1) (k := k))

/-- If a terminal right cavity width is larger than the held block itself,
some earlier fresh generation is nonempty. -/
theorem exists_freshRightTargetCavityWidth_of_held_card_lt
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card <
      (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    ∃ j < k, (freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P j).Nonempty := by
  classical
  by_contra hnone
  have hnone' : ∀ j < k, ¬(freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P j).Nonempty := by
    intro j hj hnonempty
    exact hnone ⟨j, hj, hnonempty⟩
  have hempty : (Finset.range k).biUnion
      (freshRightTargetCavityWidth (foodLength := foodLength) Cat T P) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
      exact (hnone' j (Finset.mem_range.mp hj) ⟨x, hxj⟩).elim
    · intro hx
      simp at hx
  have hsub := rightTargetCavityWidth_subset_held_union_fresh
    (foodLength := foodLength) Cat T P (k := k)
  rw [hempty, Finset.union_empty] at hsub
  exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hlarge

/-- Left-pool form of the first-fresh-generation extraction. -/
theorem exists_freshLeftTargetCavityWidth_of_held_card_lt
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card <
      (leftTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    ∃ j < k, (freshLeftTargetCavityWidth
      (foodLength := foodLength) Cat T P j).Nonempty := by
  have hlarge' : T.card < (rightTargetCavityWidth
      (foodLength := foodLength) Cat T (P.2, P.1) k).card := by
    simpa only [rightTargetCavityWidth_eq_left_swap, Prod.fst, Prod.snd,
      Prod.eta] using hlarge
  obtain ⟨j, hj, hnonempty⟩ :=
    exists_freshRightTargetCavityWidth_of_held_card_lt
      (foodLength := foodLength) Cat T (P.2, P.1) hlarge'
  refine ⟨j, hj, ?_⟩
  simpa only [freshRightTargetCavityWidth_eq_left_swap, Prod.fst,
    Prod.snd, Prod.eta] using hnonempty

/-- A genuine right-pool leave-one mass drop forces an earlier fresh
generation in the singleton cavity exploration. -/
theorem exists_freshRight_preclosed_singleton_of_pool_drop
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hgap : 1 ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).2.card < b) :
    ∃ j < k, (freshRightTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) {x} P j).Nonempty := by
  have hwidth := card_rightTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply exists_freshRightTargetCavityWidth_of_held_card_lt
  simpa using hgap.trans_lt hwidth

/-- Left-pool form of the leave-one mass-drop first-generation bridge. -/
theorem exists_freshLeft_preclosed_singleton_of_pool_drop
    {n foodLength k B b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hgap : 1 ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).1.card < b) :
    ∃ j < k, (freshLeftTargetCavityWidth (foodLength := foodLength)
      (closeTargetBlocks Cat T) {x} P j).Nonempty := by
  have hwidth := card_leftTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply exists_freshLeftTargetCavityWidth_of_held_card_lt
  simpa using hgap.trans_lt hwidth

/-- Cardinality form of the finite right-generation cover. -/
theorem card_rightTargetCavityWidth_le_held_add_sum_fresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card ≤
      T.card + ∑ j ∈ Finset.range k,
        (freshRightTargetCavityWidth
          (foodLength := foodLength) Cat T P j).card := by
  classical
  calc
    (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card ≤
        (T ∪ (Finset.range k).biUnion
          (freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P)).card :=
      Finset.card_le_card (rightTargetCavityWidth_subset_held_union_fresh
        (foodLength := foodLength) Cat T P)
    _ ≤ T.card + ((Finset.range k).biUnion
          (freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P)).card :=
      Finset.card_union_le _ _
    _ ≤ T.card + ∑ j ∈ Finset.range k,
          (freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P j).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le T.card

/-- Left-pool cardinality cover. -/
theorem card_leftTargetCavityWidth_le_held_add_sum_fresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    (leftTargetCavityWidth (foodLength := foodLength) Cat T P k).card ≤
      T.card + ∑ j ∈ Finset.range k,
        (freshLeftTargetCavityWidth
          (foodLength := foodLength) Cat T P j).card := by
  have h := card_rightTargetCavityWidth_le_held_add_sum_fresh
    (foodLength := foodLength) Cat T (P.2, P.1) (k := k)
  simpa only [rightTargetCavityWidth_eq_left_swap,
    freshRightTargetCavityWidth_eq_left_swap, Prod.fst, Prod.snd,
    Prod.eta] using h

/-- Horizon-free right-width cover: the terminal discrepancy is bounded by
the held block plus the cardinality of the union of all prior fresh sets. -/
theorem card_rightTargetCavityWidth_le_held_add_allFresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card ≤
      T.card + ((Finset.range k).biUnion
        (freshRightTargetCavityWidth
          (foodLength := foodLength) Cat T P)).card := by
  classical
  calc
    _ ≤ (T ∪ (Finset.range k).biUnion
          (freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P)).card :=
      Finset.card_le_card (rightTargetCavityWidth_subset_held_union_fresh
        (foodLength := foodLength) Cat T P)
    _ ≤ _ := Finset.card_union_le _ _

/-- A large terminal right width yields a large union of earlier fresh
targets, without dividing by the number of pruning rounds. -/
theorem large_allFreshRightTargetCavityWidth
    {n foodLength k t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card + t <
      (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    t < ((Finset.range k).biUnion
      (freshRightTargetCavityWidth
        (foodLength := foodLength) Cat T P)).card := by
  have hcover := card_rightTargetCavityWidth_le_held_add_allFresh
    (foodLength := foodLength) Cat T P (k := k)
  omega

/-- Left-pool horizon-free fresh-union extraction. -/
theorem large_allFreshLeftTargetCavityWidth
    {n foodLength k t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card + t <
      (leftTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    t < ((Finset.range k).biUnion
      (freshLeftTargetCavityWidth
        (foodLength := foodLength) Cat T P)).card := by
  have hlarge' : T.card + t <
      (rightTargetCavityWidth (foodLength := foodLength)
        Cat T (P.2, P.1) k).card := by
    simpa only [rightTargetCavityWidth_eq_left_swap, Prod.fst,
      Prod.snd, Prod.eta] using hlarge
  have h := large_allFreshRightTargetCavityWidth
    (foodLength := foodLength) Cat T (P.2, P.1) hlarge'
  have heq : (Finset.range k).biUnion
      (freshRightTargetCavityWidth
        (foodLength := foodLength) Cat T (P.2, P.1)) =
      (Finset.range k).biUnion
        (freshLeftTargetCavityWidth
          (foodLength := foodLength) Cat T P) := by
    classical
    ext y
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, hy⟩
      refine ⟨j, hj, ?_⟩
      simpa only [freshRightTargetCavityWidth_eq_left_swap, Prod.fst,
        Prod.snd, Prod.eta] using hy
    · rintro ⟨j, hj, hy⟩
      refine ⟨j, hj, ?_⟩
      simpa only [freshRightTargetCavityWidth_eq_left_swap, Prod.fst,
        Prod.snd, Prod.eta] using hy
  rw [← heq]
  exact h

/-- Pigeonhole extraction of a large earlier right fresh batch. -/
theorem exists_large_freshRightTargetCavityWidth
    {n foodLength k t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card + k * t <
      (rightTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    ∃ j < k, t < (freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P j).card := by
  by_contra hnone
  have hall : ∀ j < k, (freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P j).card ≤ t := by
    intro j hj
    exact Nat.le_of_not_gt fun hgt => hnone ⟨j, hj, hgt⟩
  have hsum : ∑ j ∈ Finset.range k,
      (freshRightTargetCavityWidth
        (foodLength := foodLength) Cat T P j).card ≤
      ∑ _j ∈ Finset.range k, t := by
    apply Finset.sum_le_sum
    intro j hj
    exact hall j (Finset.mem_range.mp hj)
  have hcover := card_rightTargetCavityWidth_le_held_add_sum_fresh
    (foodLength := foodLength) Cat T P (k := k)
  have hle : (rightTargetCavityWidth
      (foodLength := foodLength) Cat T P k).card ≤ T.card + k * t := by
    calc
      _ ≤ T.card + ∑ j ∈ Finset.range k,
          (freshRightTargetCavityWidth
            (foodLength := foodLength) Cat T P j).card := hcover
      _ ≤ T.card + ∑ _j ∈ Finset.range k, t :=
        Nat.add_le_add_left hsum T.card
      _ = T.card + k * t := by simp
  exact (Nat.not_lt_of_ge hle) hlarge

/-- Left-pool large-batch pigeonhole extraction. -/
theorem exists_large_freshLeftTargetCavityWidth
    {n foodLength k t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hlarge : T.card + k * t <
      (leftTargetCavityWidth (foodLength := foodLength) Cat T P k).card) :
    ∃ j < k, t < (freshLeftTargetCavityWidth
      (foodLength := foodLength) Cat T P j).card := by
  have hlarge' : T.card + k * t < (rightTargetCavityWidth
      (foodLength := foodLength) Cat T (P.2, P.1) k).card := by
    simpa only [rightTargetCavityWidth_eq_left_swap, Prod.fst,
      Prod.snd, Prod.eta] using hlarge
  obtain ⟨j, hj, hjlarge⟩ := exists_large_freshRightTargetCavityWidth
    (foodLength := foodLength) Cat T (P.2, P.1) hlarge'
  refine ⟨j, hj, ?_⟩
  simpa only [freshRightTargetCavityWidth_eq_left_swap, Prod.fst,
    Prod.snd, Prod.eta] using hjlarge

/-- Quantitative right-pool first-exit bridge: a leave-one mass gap large
enough to cover `k` generations forces one fresh batch larger than `t`. -/
theorem exists_large_freshRight_preclosed_singleton_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : 1 + k * t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).2.card < b) :
    ∃ j < k, t < (freshRightTargetCavityWidth
      (foodLength := foodLength) (closeTargetBlocks Cat T) {x} P j).card := by
  have hwidth := card_rightTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply exists_large_freshRightTargetCavityWidth
  simpa using hbudget.trans_lt hwidth

/-- Left-pool quantitative first-exit bridge. -/
theorem exists_large_freshLeft_preclosed_singleton_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : 1 + k * t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).1.card < b) :
    ∃ j < k, t < (freshLeftTargetCavityWidth
      (foodLength := foodLength) (closeTargetBlocks Cat T) {x} P j).card := by
  have hwidth := card_leftTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply exists_large_freshLeftTargetCavityWidth
  simpa using hbudget.trans_lt hwidth

/-- Horizon-free right-pool pool-drop bridge.  The loss forces a large union
of fresh targets even when the deterministic stabilization horizon is large. -/
theorem large_allFreshRight_preclosed_singleton_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : 1 + t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).2.card < b) :
    t < ((Finset.range k).biUnion
      (freshRightTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) {x} P)).card := by
  have hwidth := card_rightTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply large_allFreshRightTargetCavityWidth
  simpa using hbudget.trans_lt hwidth

/-- Left-pool horizon-free singleton pool-drop bridge. -/
theorem large_allFreshLeft_preclosed_singleton_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) (x : Molecule n)
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : 1 + t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hleave :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ {x})) P k).1.card < b) :
    t < ((Finset.range k).biUnion
      (freshLeftTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) {x} P)).card := by
  have hwidth := card_leftTargetCavityWidth_preclosed_singleton_gt_sub
    Cat T x P hbB hbase hleave
  apply large_allFreshLeftTargetCavityWidth
  simpa using hbudget.trans_lt hwidth

/-- Direct arbitrary-block right-pool recursion.  If the pool loss exceeds
the size of the held batch by `t`, the union of all genuinely new cavity
targets has size greater than `t`; no singleton averaging is required. -/
theorem large_allFreshRight_preclosed_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : U.card + t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hdeep :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).2.card < b) :
    t < ((Finset.range k).biUnion
      (freshRightTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) U P)).card := by
  have hwidth := card_rightTargetCavityWidth_preclosed_gt_sub
    Cat T U P hbB hbase hdeep
  apply large_allFreshRightTargetCavityWidth
  exact hbudget.trans_lt hwidth

/-- Direct arbitrary-block left-pool recursion. -/
theorem large_allFreshLeft_preclosed_of_pool_drop
    {n foodLength k B b t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbB : b ≤ B) (hbudget : U.card + t ≤ B - b)
    (hbase : B ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hdeep :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).1.card < b) :
    t < ((Finset.range k).biUnion
      (freshLeftTargetCavityWidth (foodLength := foodLength)
        (closeTargetBlocks Cat T) U P)).card := by
  have hwidth := card_leftTargetCavityWidth_preclosed_gt_sub
    Cat T U P hbB hbase hdeep
  apply large_allFreshLeftTargetCavityWidth
  exact hbudget.trans_lt hwidth

end HordijkSteelThreshold

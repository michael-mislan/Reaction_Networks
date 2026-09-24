import proofs.HordijkSteelThreshold.LeaveOneCavityProfile

namespace HordijkSteelThreshold

/-- Finite first-crossing principle with no monotonicity assumption: if a
set-valued exploration starts above a threshold and ends below it, some single
insertion crosses the threshold. -/
theorem exists_insert_crossing_of_empty_ge_full_lt
    {α : Type*} [DecidableEq α] (f : Finset α → Nat)
    (U : Finset α) (b : Nat) (h0 : b ≤ f ∅) (hU : f U < b) :
    ∃ V ⊆ U, ∃ x ∈ U \ V, b ≤ f V ∧ f (insert x V) < b := by
  induction U using Finset.induction_on with
  | empty =>
      omega
  | @insert a U ha ih =>
      by_cases hprev : f U < b
      · obtain ⟨V, hVU, x, hx, hV, hxV⟩ := ih hprev
        refine ⟨V, hVU.trans (Finset.subset_insert a U), x, ?_, hV, hxV⟩
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hx).1,
            (Finset.mem_sdiff.mp hx).2⟩
      · refine ⟨U, Finset.subset_insert a U, a, ?_,
          Nat.le_of_not_gt hprev, hU⟩
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self a U, ha⟩

/-- If every insertion into a subset of `U` loses at most `delta`, the total
loss from the empty set to `U` is at most `|U| * delta`.  No monotonicity of
`f` is needed. -/
theorem empty_le_full_add_card_mul_of_insert_le
    {alpha : Type*} [DecidableEq alpha] (f : Finset alpha → Nat)
    (U : Finset alpha) (delta : Nat)
    (hstep : ∀ V ⊆ U, ∀ x ∈ U \ V,
      f V ≤ f (insert x V) + delta) :
    f ∅ ≤ f U + U.card * delta := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert a U ha ih =>
      have hstepU : ∀ V ⊆ U, ∀ x ∈ U \ V,
          f V ≤ f (insert x V) + delta := by
        intro V hVU x hx
        apply hstep V (hVU.trans (Finset.subset_insert a U)) x
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hx).1,
            (Finset.mem_sdiff.mp hx).2⟩
      have hprefix := ih hstepU
      have hlast : f U ≤ f (insert a U) + delta := by
        apply hstep U (Finset.subset_insert a U) a
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self a U, ha⟩
      rw [Finset.card_insert_of_notMem ha]
      calc
        f ∅ ≤ f U + U.card * delta := hprefix
        _ ≤ (f (insert a U) + delta) + U.card * delta :=
          Nat.add_le_add_right hlast _
        _ = f (insert a U) + (U.card + 1) * delta := by
          simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Quantitative insertion principle: if the total loss across `U` exceeds
`|U| * delta`, some single insertion loses more than `delta`. -/
theorem exists_insert_drop_gt_of_full_gap
    {alpha : Type*} [DecidableEq alpha] (f : Finset alpha → Nat)
    (U : Finset alpha) (delta : Nat)
    (hgap : f U + U.card * delta < f ∅) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      f (insert x V) + delta < f V := by
  by_contra hnone
  have hstep : ∀ V ⊆ U, ∀ x ∈ U \ V,
      f V ≤ f (insert x V) + delta := by
    intro V hVU x hx
    apply Nat.le_of_not_gt
    intro hdrop
    exact hnone ⟨V, hVU, x, hx, hdrop⟩
  have htotal := empty_le_full_add_card_mul_of_insert_le f U delta hstep
  omega

open RAF RAF.Polymer RAF.Concrete

/-- First subset at which closing an additional target block crosses the
right-pool mass floor. -/
theorem exists_rightPool_insert_crossing
    {n foodLength k b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbase : b ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2.card)
    (hfull :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).2.card < b) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      b ≤ (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ V)) P k).2.card ∧
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ insert x V)) P k).2.card < b := by
  let f : Finset (Molecule n) → Nat := fun V =>
    (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).2.card
  have h0 : b ≤ f ∅ := by simpa [f] using hbase
  have hU : f U < b := by simpa [f] using hfull
  simpa only [f] using exists_insert_crossing_of_empty_ge_full_lt f U b h0 hU

/-- Left-pool form of the target-subset first crossing. -/
theorem exists_leftPool_insert_crossing
    {n foodLength k b : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbase : b ≤
      (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1.card)
    (hfull :
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ U)) P k).1.card < b) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      b ≤ (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ V)) P k).1.card ∧
      (crossPoolIter foodLength
        (closeTargetBlocks Cat (T ∪ insert x V)) P k).1.card < b := by
  let f : Finset (Molecule n) → Nat := fun V =>
    (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).1.card
  have h0 : b ≤ f ∅ := by simpa [f] using hbase
  have hU : f U < b := by simpa [f] using hfull
  simpa only [f] using exists_insert_crossing_of_empty_ge_full_lt f U b h0 hU

/-- A large total right-pool loss across a target batch contains a single
insertion with a proportionally large loss. -/
theorem exists_rightPool_insert_drop_gt
    {n foodLength k delta : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).2.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ insert x V)) P k).2.card + delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ V)) P k).2.card := by
  let f : Finset (Molecule n) → Nat := fun V =>
    (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).2.card
  have hgap' : f U + U.card * delta < f ∅ := by simpa [f] using hgap
  simpa only [f] using exists_insert_drop_gt_of_full_gap f U delta hgap'

/-- Mass-band bridge for the right pool.  If closing a target batch loses
more than `|U| * delta` pool elements and `delta` pays for `k` generations,
then at an intermediate closure one target forces a fresh generation larger
than `t`. -/
theorem exists_large_freshRight_of_target_batch_pool_gap
    {n foodLength k delta t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbudget : 1 + k * t ≤ delta)
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).2.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V, ∃ j < k,
      t < (freshRightTargetCavityWidth
        (foodLength := foodLength) (closeTargetBlocks Cat (T ∪ V))
        {x} P j).card := by
  obtain ⟨V, hVU, x, hx, hdrop⟩ :=
    exists_rightPool_insert_drop_gt Cat T U P hgap
  let B := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ V)) P k).2.card
  let b := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ insert x V)) P k).2.card + 1
  have hbB : b ≤ B := by
    dsimp [b, B]
    omega
  have hbudget' : 1 + k * t ≤ B - b := by
    dsimp [b, B]
    omega
  have hbase : B ≤ (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).2.card := by rfl
  have hunion : (T ∪ V) ∪ {x} = T ∪ insert x V := by
    ext y
    simp
  have hleave : (crossPoolIter foodLength
      (closeTargetBlocks Cat ((T ∪ V) ∪ {x})) P k).2.card < b := by
    rw [hunion]
    exact Nat.lt_succ_self _
  obtain ⟨j, hj, hjlarge⟩ :=
    exists_large_freshRight_preclosed_singleton_of_pool_drop
      Cat (T ∪ V) x P hbB hbudget' hbase hleave
  exact ⟨V, hVU, x, hx, j, hj, hjlarge⟩

/-- Left-pool form of the quantitative insertion-drop principle. -/
theorem exists_leftPool_insert_drop_gt
    {n foodLength k delta : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).1.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).1.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ insert x V)) P k).1.card + delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ V)) P k).1.card := by
  let f : Finset (Molecule n) → Nat := fun V =>
    (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).1.card
  have hgap' : f U + U.card * delta < f ∅ := by simpa [f] using hgap
  simpa only [f] using exists_insert_drop_gt_of_full_gap f U delta hgap'

/-- Left-pool mass-band bridge from aggregate target-batch loss to a large
fresh generation at an intermediate singleton closure. -/
theorem exists_large_freshLeft_of_target_batch_pool_gap
    {n foodLength k delta t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbudget : 1 + k * t ≤ delta)
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).1.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).1.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V, ∃ j < k,
      t < (freshLeftTargetCavityWidth
        (foodLength := foodLength) (closeTargetBlocks Cat (T ∪ V))
        {x} P j).card := by
  obtain ⟨V, hVU, x, hx, hdrop⟩ :=
    exists_leftPool_insert_drop_gt Cat T U P hgap
  let B := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ V)) P k).1.card
  let b := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ insert x V)) P k).1.card + 1
  have hbB : b ≤ B := by
    dsimp [b, B]
    omega
  have hbudget' : 1 + k * t ≤ B - b := by
    dsimp [b, B]
    omega
  have hbase : B ≤ (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).1.card := by rfl
  have hunion : (T ∪ V) ∪ {x} = T ∪ insert x V := by
    ext y
    simp
  have hleave : (crossPoolIter foodLength
      (closeTargetBlocks Cat ((T ∪ V) ∪ {x})) P k).1.card < b := by
    rw [hunion]
    exact Nat.lt_succ_self _
  obtain ⟨j, hj, hjlarge⟩ :=
    exists_large_freshLeft_preclosed_singleton_of_pool_drop
      Cat (T ∪ V) x P hbB hbudget' hbase hleave
  exact ⟨V, hVU, x, hx, j, hj, hjlarge⟩

/-- Horizon-free right mass-band recursion.  A batch causing aggregate loss
greater than `|U|*delta` creates an intermediate singleton whose union of all
fresh generations has size greater than `t`, with no stabilization-horizon
factor. -/
theorem large_allFreshRight_of_target_batch_pool_gap
    {n foodLength k delta t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbudget : 1 + t ≤ delta)
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).2.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      t < ((Finset.range k).biUnion
        (freshRightTargetCavityWidth (foodLength := foodLength)
          (closeTargetBlocks Cat (T ∪ V)) {x} P)).card := by
  obtain ⟨V, hVU, x, hx, hdrop⟩ :=
    exists_rightPool_insert_drop_gt Cat T U P hgap
  let B := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ V)) P k).2.card
  let b := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ insert x V)) P k).2.card + 1
  have hbB : b ≤ B := by
    dsimp [b, B]
    omega
  have hbudget' : 1 + t ≤ B - b := by
    dsimp [b, B]
    omega
  have hbase : B ≤ (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).2.card := by rfl
  have hunion : (T ∪ V) ∪ {x} = T ∪ insert x V := by
    ext y
    simp
  have hleave : (crossPoolIter foodLength
      (closeTargetBlocks Cat ((T ∪ V) ∪ {x})) P k).2.card < b := by
    rw [hunion]
    exact Nat.lt_succ_self _
  refine ⟨V, hVU, x, hx, ?_⟩
  exact large_allFreshRight_preclosed_singleton_of_pool_drop
    Cat (T ∪ V) x P hbB hbudget' hbase hleave

/-- Left-pool horizon-free mass-band recursion. -/
theorem large_allFreshLeft_of_target_batch_pool_gap
    {n foodLength k delta t : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hbudget : 1 + t ≤ delta)
    (hgap :
      (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).1.card +
          U.card * delta <
        (crossPoolIter foodLength
          (closeTargetBlocks Cat T) P k).1.card) :
    ∃ V ⊆ U, ∃ x ∈ U \ V,
      t < ((Finset.range k).biUnion
        (freshLeftTargetCavityWidth (foodLength := foodLength)
          (closeTargetBlocks Cat (T ∪ V)) {x} P)).card := by
  obtain ⟨V, hVU, x, hx, hdrop⟩ :=
    exists_leftPool_insert_drop_gt Cat T U P hgap
  let B := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ V)) P k).1.card
  let b := (crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ insert x V)) P k).1.card + 1
  have hbB : b ≤ B := by
    dsimp [b, B]
    omega
  have hbudget' : 1 + t ≤ B - b := by
    dsimp [b, B]
    omega
  have hbase : B ≤ (crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ V)) P k).1.card := by rfl
  have hunion : (T ∪ V) ∪ {x} = T ∪ insert x V := by
    ext y
    simp
  have hleave : (crossPoolIter foodLength
      (closeTargetBlocks Cat ((T ∪ V) ∪ {x})) P k).1.card < b := by
    rw [hunion]
    exact Nat.lt_succ_self _
  refine ⟨V, hVU, x, hx, ?_⟩
  exact large_allFreshLeft_preclosed_singleton_of_pool_drop
    Cat (T ∪ V) x P hbB hbudget' hbase hleave

end HordijkSteelThreshold

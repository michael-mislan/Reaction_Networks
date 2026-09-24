import proofs.HordijkSteelThreshold.TwoPoolPruning

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- Molecules retained by ordinary pruning but lost when the product-target
block `T` is closed. -/
noncomputable def leftTargetCavityWidth {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :=
  (crossPoolIter foodLength Cat P k).1 \
    (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).1

noncomputable def rightTargetCavityWidth {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :=
  (crossPoolIter foodLength Cat P k).2 \
    (crossPoolIter foodLength (closeTargetBlocks Cat T) P k).2

@[simp] theorem leftTargetCavityWidth_zero {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    leftTargetCavityWidth (foodLength := foodLength) Cat T P 0 = ∅ := by
  simp [leftTargetCavityWidth, crossPoolIter]

@[simp] theorem rightTargetCavityWidth_zero {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    rightTargetCavityWidth (foodLength := foodLength) Cat T P 0 = ∅ := by
  simp [rightTargetCavityWidth, crossPoolIter]

/-- Exact deterministic genealogy of a new left cavity discrepancy.  Away
from the held target block, it must descend from a prior factor discrepancy or
from a prior opposite-pool catalyst discrepancy. -/
theorem mem_leftTargetCavityWidth_succ_imp {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ leftTargetCavityWidth
      (foodLength := foodLength) Cat T P (k + 1)) :
    x ∈ leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
      x ∈ T ∨
      ∃ r : Reaction n,
        reactionProduct r = x ∧
        (reactionLeft r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
          reactionRight r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
          ∃ y ∈ rightTargetCavityWidth
              (foodLength := foodLength) Cat T P k, Cat y r) := by
  classical
  let A := crossPoolIter foodLength Cat P k
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  have hSA := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) (closeTargetBlocks_le Cat T)
    (Finset.Subset.rfl) (Finset.Subset.rfl) k
  have hxActualSucc : x ∈ (crossPoolStep foodLength Cat A).1 := by
    exact (Finset.mem_sdiff.mp hx).1
  have hxNotClosedSucc : x ∉
      (crossPoolStep foodLength (closeTargetBlocks Cat T) S).1 := by
    exact (Finset.mem_sdiff.mp hx).2
  have hxA : x ∈ A.1 := crossPoolStep_left_subset Cat A hxActualSucc
  by_cases hxS : x ∈ S.1
  · right
    by_cases hxT : x ∈ T
    · exact Or.inl hxT
    · right
      have hsurvive := (Finset.mem_filter.mp hxActualSucc).2
      rcases hsurvive with hfood | ⟨r, hprod, hleft, hright, y, hyA, hcat⟩
      · exfalso
        apply hxNotClosedSucc
        exact Finset.mem_filter.mpr ⟨hxS, Or.inl hfood⟩
      · refine ⟨r, hprod, ?_⟩
        by_cases hleftW : reactionLeft r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k
        · exact Or.inl hleftW
        by_cases hrightW : reactionRight r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k
        · exact Or.inr (Or.inl hrightW)
        by_cases hyW : y ∈ rightTargetCavityWidth
            (foodLength := foodLength) Cat T P k
        · exact Or.inr (Or.inr ⟨y, hyW, hcat⟩)
        exfalso
        apply hxNotClosedSucc
        have hleftS : reactionLeft r ∈ S.1 ∪ S.2 := by
          rcases Finset.mem_union.mp hleft with hl | hr
          · exact Finset.mem_union_left _ (by
              by_contra hn
              exact hleftW (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨hl, hn⟩)))
          · exact Finset.mem_union_right _ (by
              by_contra hn
              exact hleftW (Finset.mem_union_right _
                (Finset.mem_sdiff.mpr ⟨hr, hn⟩)))
        have hrightS : reactionRight r ∈ S.1 ∪ S.2 := by
          rcases Finset.mem_union.mp hright with hl | hr
          · exact Finset.mem_union_left _ (by
              by_contra hn
              exact hrightW (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨hl, hn⟩)))
          · exact Finset.mem_union_right _ (by
              by_contra hn
              exact hrightW (Finset.mem_union_right _
                (Finset.mem_sdiff.mpr ⟨hr, hn⟩)))
        have hyS : y ∈ S.2 := by
          by_contra hn
          exact hyW (Finset.mem_sdiff.mpr ⟨hyA, hn⟩)
        have hcatClosed : closeTargetBlocks Cat T y r := by
          simp [closeTargetBlocks, hprod, hxT, hcat]
        exact Finset.mem_filter.mpr ⟨hxS, Or.inr
          ⟨r, hprod, hleftS, hrightS, y, hyS, hcatClosed⟩⟩
  · left
    exact Finset.mem_sdiff.mpr ⟨hxA, hxS⟩

theorem crossPoolIter_swap {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    crossPoolIter foodLength Cat (P.2, P.1) k =
      ((crossPoolIter foodLength Cat P k).2,
        (crossPoolIter foodLength Cat P k).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change crossPoolStep foodLength Cat
          (crossPoolIter foodLength Cat (P.2, P.1) k) = _
      rw [ih]
      rfl

theorem rightTargetCavityWidth_eq_left_swap {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    rightTargetCavityWidth (foodLength := foodLength) Cat T P k =
      leftTargetCavityWidth (foodLength := foodLength) Cat T (P.2, P.1) k := by
  simp only [rightTargetCavityWidth, leftTargetCavityWidth,
    crossPoolIter_swap]

/-- Right-hand version of the exact cavity genealogy. -/
theorem mem_rightTargetCavityWidth_succ_imp {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ rightTargetCavityWidth
      (foodLength := foodLength) Cat T P (k + 1)) :
    x ∈ rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
      x ∈ T ∨
      ∃ r : Reaction n,
        reactionProduct r = x ∧
        (reactionLeft r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
          reactionRight r ∈
            leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪
              rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∨
          ∃ y ∈ leftTargetCavityWidth
              (foodLength := foodLength) Cat T P k, Cat y r) := by
  have hx' : x ∈ leftTargetCavityWidth (foodLength := foodLength)
      Cat T (P.2, P.1) (k + 1) := by
    rwa [← rightTargetCavityWidth_eq_left_swap]
  rcases mem_leftTargetCavityWidth_succ_imp Cat T (P.2, P.1) hx' with
    hprev | hxT | ⟨r, hprod, hleft | hright | ⟨y, hy, hcat⟩⟩
  · left
    rwa [← rightTargetCavityWidth_eq_left_swap] at hprev
  · exact Or.inr (Or.inl hxT)
  · right; right; refine ⟨r, hprod, Or.inl ?_⟩
    simpa only [rightTargetCavityWidth_eq_left_swap,
      Finset.union_comm] using hleft
  · right; right; refine ⟨r, hprod, Or.inr (Or.inl ?_)⟩
    simpa only [rightTargetCavityWidth_eq_left_swap,
      Finset.union_comm] using hright
  · right; right; refine ⟨r, hprod, Or.inr (Or.inr ⟨y, ?_, hcat⟩)⟩
    simpa only [rightTargetCavityWidth_eq_left_swap] using hy

/-- Cavity discrepancies first appearing at the next left step, excluding the
held target block itself. -/
noncomputable def freshLeftTargetCavityWidth {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :=
  leftTargetCavityWidth (foodLength := foodLength) Cat T P (k + 1) \
    (leftTargetCavityWidth (foodLength := foodLength) Cat T P k ∪ T)

theorem catalystPoolFamilyOpen_closeTargetBlocks_iff_of_product_not_mem
    {n : Nat} (Cat : Catalysis (Molecule n) (Reaction n))
    (T C : Finset (Molecule n)) (x : Molecule n) (hxT : x ∉ T)
    (R : Finset (Reaction n))
    (hprod : ∀ r ∈ R, reactionProduct r = x) :
    catalystPoolFamilyOpen (fun z => closeTargetBlocks Cat T z.1 z.2) C R ↔
      catalystPoolFamilyOpen (fun z => Cat z.1 z.2) C R := by
  constructor
  · rintro ⟨r, hr, y, hy, hcat⟩
    exact ⟨r, hr, y, hy, hcat.1⟩
  · rintro ⟨r, hr, y, hy, hcat⟩
    refine ⟨r, hr, y, hy, ?_⟩
    exact ⟨hcat, by simpa [hprod r hr] using hxT⟩

/-- Every genuinely new non-held cavity discrepancy is a literal barrier:
its whole viable family is closed against the previous closed-cavity
opposite pool. -/
theorem freshLeftTargetCavityWidth_familyClosed {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ freshLeftTargetCavityWidth
      (foodLength := foodLength) Cat T P k) :
    let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
    foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2) S.2
        (crossViableReactions S.1 S.2 x) := by
  classical
  let A := crossPoolIter foodLength Cat P k
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  have hxNext := (Finset.mem_sdiff.mp hx).1
  have hxOldNot := (Finset.mem_sdiff.mp hx).2
  have hxNotOldWidth : x ∉ leftTargetCavityWidth
      (foodLength := foodLength) Cat T P k := by
    intro h
    exact hxOldNot (Finset.mem_union_left _ h)
  have hxT : x ∉ T := by
    intro h
    exact hxOldNot (Finset.mem_union_right _ h)
  have hxActualNext := (Finset.mem_sdiff.mp hxNext).1
  have hxNotClosedNext := (Finset.mem_sdiff.mp hxNext).2
  have hxA : x ∈ A.1 := crossPoolStep_left_subset Cat A hxActualNext
  have hxS : x ∈ S.1 := by
    by_contra hnot
    exact hxNotOldWidth (Finset.mem_sdiff.mpr ⟨hxA, hnot⟩)
  have hbarrier := (not_mem_crossPoolStep_left_iff
    (closeTargetBlocks Cat T) S.1 S.2 hxS).mp hxNotClosedNext
  refine ⟨hbarrier.1, ?_⟩
  have hopen := catalystPoolFamilyOpen_closeTargetBlocks_iff_of_product_not_mem
    Cat T S.2 x hxT (crossViableReactions S.1 S.2 x)
    (fun r hr => (mem_crossViableReactions S.1 S.2 x r).mp hr |>.1)
  exact fun h => hbarrier.2 (hopen.mpr h)

noncomputable def freshRightTargetCavityWidth {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :=
  rightTargetCavityWidth (foodLength := foodLength) Cat T P (k + 1) \
    (rightTargetCavityWidth (foodLength := foodLength) Cat T P k ∪ T)

theorem freshRightTargetCavityWidth_eq_left_swap {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    freshRightTargetCavityWidth (foodLength := foodLength) Cat T P k =
      freshLeftTargetCavityWidth (foodLength := foodLength)
        Cat T (P.2, P.1) k := by
  simp only [freshRightTargetCavityWidth, freshLeftTargetCavityWidth,
    rightTargetCavityWidth_eq_left_swap]

theorem freshRightTargetCavityWidth_familyClosed {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P k) :
    let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
    foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2) S.1
        (crossViableReactions S.2 S.1 x) := by
  have hx' : x ∈ freshLeftTargetCavityWidth (foodLength := foodLength)
      Cat T (P.2, P.1) k := by
    rwa [← freshRightTargetCavityWidth_eq_left_swap]
  have h := freshLeftTargetCavityWidth_familyClosed Cat T (P.2, P.1) hx'
  simpa only [crossPoolIter_swap] using h

theorem closeTargetBlocks_union {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n)) :
    closeTargetBlocks (closeTargetBlocks Cat T) U =
      closeTargetBlocks Cat (T ∪ U) := by
  funext y r
  apply propext
  simp [closeTargetBlocks, and_assoc]

theorem crossViableReactions_mono {n : Nat}
    {A A' B B' : Finset (Molecule n)}
    (hA : A ⊆ A') (hB : B ⊆ B') (x : Molecule n) :
    crossViableReactions A B x ⊆ crossViableReactions A' B' x := by
  classical
  intro r hr
  have h := (mem_crossViableReactions A B x r).mp hr
  exact (mem_crossViableReactions A' B' x r).mpr
    ⟨h.1, Finset.union_subset_union hA hB h.2.1,
      Finset.union_subset_union hA hB h.2.2⟩

/-- Cross-pool pruning is antitone in its iteration counter. -/
theorem crossPoolIter_mono_time {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {j k : Nat} (hjk : j ≤ k) :
    (crossPoolIter foodLength Cat P k).1 ⊆
        (crossPoolIter foodLength Cat P j).1 ∧
      (crossPoolIter foodLength Cat P k).2 ⊆
        (crossPoolIter foodLength Cat P j).2 := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction l with
  | zero => simp
  | succ l ih =>
      have hs := crossPoolIter_succ_subset (foodLength := foodLength)
        Cat P (j + l)
      simpa [Nat.add_assoc] using And.intro
        (hs.1.trans ih.1) (hs.2.trans ih.2)

theorem catalystPoolFamilyOpen_mono {n : Nat}
    (ω : AmbientCoord n → Prop)
    {C C' : Finset (Molecule n)} {R R' : Finset (Reaction n)}
    (hC : C ⊆ C') (hR : R ⊆ R')
    (hopen : catalystPoolFamilyOpen ω C R) :
    catalystPoolFamilyOpen ω C' R' := by
  rcases hopen with ⟨r, hr, y, hy, hcat⟩
  exact ⟨r, hR hr, y, hC hy, hcat⟩

/-- Closing target coordinates outside both current pools does not change one
pruning step on those pools. -/
theorem crossPoolStep_closeTargetBlocks_eq_of_disjoint
    {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (U A B : Finset (Molecule n))
    (hUA : Disjoint U A) (hUB : Disjoint U B) :
    crossPoolStep foodLength (closeTargetBlocks Cat U) (A, B) =
      crossPoolStep foodLength Cat (A, B) := by
  classical
  apply Prod.ext
  · ext x
    simp only [crossPoolStep, Finset.mem_filter]
    constructor
    · rintro ⟨hxA, hxsurv⟩
      refine ⟨hxA, ?_⟩
      exact (crossLeftSurvives_targetBlock_sandwich_eq
        Cat U A B (fun hxU => Finset.disjoint_left.mp hUA hxU hxA)).1.mp hxsurv
    · rintro ⟨hxA, hxsurv⟩
      refine ⟨hxA, ?_⟩
      exact (crossLeftSurvives_targetBlock_sandwich_eq
        Cat U A B (fun hxU => Finset.disjoint_left.mp hUA hxU hxA)).1.mpr hxsurv
  · ext x
    simp only [crossPoolStep, Finset.mem_filter]
    constructor
    · rintro ⟨hxB, hxsurv⟩
      refine ⟨hxB, ?_⟩
      exact (crossLeftSurvives_targetBlock_sandwich_eq
        Cat U B A (fun hxU => Finset.disjoint_left.mp hUB hxU hxB)).1.mp hxsurv
    · rintro ⟨hxB, hxsurv⟩
      refine ⟨hxB, ?_⟩
      exact (crossLeftSurvives_targetBlock_sandwich_eq
        Cat U B A (fun hxU => Finset.disjoint_left.mp hUB hxU hxB)).1.mpr hxsurv

/-- A fixed pair contained in the initial pair remains contained in every
iterate of the same pruning map. -/
theorem fixedPair_subset_crossPoolIter
    {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (S P : Finset (Molecule n) × Finset (Molecule n))
    (hfix : crossPoolStep foodLength Cat S = S)
    (hleft : S.1 ⊆ P.1) (hright : S.2 ⊆ P.2) (k : Nat) :
    S.1 ⊆ (crossPoolIter foodLength Cat P k).1 ∧
      S.2 ⊆ (crossPoolIter foodLength Cat P k).2 := by
  induction k with
  | zero => exact ⟨hleft, hright⟩
  | succ k ih =>
      have hmono := crossPoolStep_mono (foodLength := foodLength)
        (Cat := Cat) (Cat' := Cat)
        (fun _ _ h => h) ih.1 ih.2
      rw [hfix] at hmono
      exact hmono

/-- Terminal diagonal cavity idempotence.  Once the `T`-closed pruning state
is fixed, closing any target subset of its terminal cavity width leaves that
fixed state unchanged: none of those targets belongs to either retained pool,
so no reaction producing a retained molecule is removed. -/
theorem crossPoolIter_close_terminalCavity_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U A : Finset (Molecule n))
    (hfix : crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) (k + 1) =
      crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) k)
    (hU : U ⊆ leftTargetCavityWidth
      (foodLength := foodLength) Cat T (A, A) k) :
    crossPoolIter foodLength
        (closeTargetBlocks (closeTargetBlocks Cat T) U) (A, A) k =
      crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) k := by
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) k
  have hdiag : S.1 = S.2 := by
    exact crossPoolIter_diagonal (closeTargetBlocks Cat T) A
  have hUSleft : Disjoint U S.1 := by
    rw [Finset.disjoint_left]
    intro x hxU hxS
    exact (Finset.mem_sdiff.mp (hU hxU)).2 hxS
  have hUSright : Disjoint U S.2 := by
    rw [Finset.disjoint_left]
    intro x hxU hxS
    apply Finset.disjoint_left.mp hUSleft hxU
    rw [hdiag]
    exact hxS
  have hSfix : crossPoolStep foodLength (closeTargetBlocks Cat T) S = S := by
    exact hfix
  have hSfixDeep :
      crossPoolStep foodLength
        (closeTargetBlocks (closeTargetBlocks Cat T) U) S = S := by
    rw [crossPoolStep_closeTargetBlocks_eq_of_disjoint
      (closeTargetBlocks Cat T) U S.1 S.2 hUSleft hUSright]
    exact hSfix
  have hSinit := crossPoolIter_mono_time (foodLength := foodLength)
    (closeTargetBlocks Cat T) (A, A) (Nat.zero_le k)
  have hlower := fixedPair_subset_crossPoolIter
    (closeTargetBlocks (closeTargetBlocks Cat T) U) S (A, A)
    hSfixDeep hSinit.1 hSinit.2 k
  have hupper := crossPoolIter_mono (foodLength := foodLength)
    (P := (A, A)) (Q := (A, A))
    (closeTargetBlocks_le (closeTargetBlocks Cat T) U)
    (Finset.Subset.rfl) (Finset.Subset.rfl) k
  apply Prod.ext
  · exact Finset.Subset.antisymm hupper.1 hlower.1
  · exact Finset.Subset.antisymm hupper.2 hlower.2

/-- Union-normalized form used by the common-cavity probability theorems. -/
theorem crossPoolIter_close_terminalCavity_union_eq
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U A : Finset (Molecule n))
    (hfix : crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) (k + 1) =
      crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) k)
    (hU : U ⊆ leftTargetCavityWidth
      (foodLength := foodLength) Cat T (A, A) k) :
    crossPoolIter foodLength (closeTargetBlocks Cat (T ∪ U)) (A, A) k =
      crossPoolIter foodLength (closeTargetBlocks Cat T) (A, A) k := by
  rw [← closeTargetBlocks_union]
  exact crossPoolIter_close_terminalCavity_eq Cat T U A hfix hU

/-- A fresh discrepancy remains a closed-family certificate in the deeper
leave-one-generation cavity that also closes the discrepancy's own target
block. -/
theorem freshLeftTargetCavityWidth_leaveOne_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ freshLeftTargetCavityWidth
      (foodLength := foodLength) Cat T P k) :
    let Sx := crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ {x})) P k
    foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2) Sx.2
        (crossViableReactions Sx.1 Sx.2 x) := by
  classical
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  let Sx := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ {x})) P k
  have hbase := freshLeftTargetCavityWidth_familyClosed Cat T P hx
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ {x}) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  refine ⟨hbase.1, ?_⟩
  intro hopen
  apply hbase.2
  exact catalystPoolFamilyOpen_mono (fun z => Cat z.1 z.2)
    hsub.2 (crossViableReactions_mono hsub.1 hsub.2 x) hopen

theorem freshRightTargetCavityWidth_leaveOne_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    {x : Molecule n}
    (hx : x ∈ freshRightTargetCavityWidth
      (foodLength := foodLength) Cat T P k) :
    let Sx := crossPoolIter foodLength
      (closeTargetBlocks Cat (T ∪ {x})) P k
    foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2) Sx.1
        (crossViableReactions Sx.2 Sx.1 x) := by
  classical
  let S := crossPoolIter foodLength (closeTargetBlocks Cat T) P k
  let Sx := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ {x})) P k
  have hbase := freshRightTargetCavityWidth_familyClosed Cat T P hx
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ {x}) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  refine ⟨hbase.1, ?_⟩
  intro hopen
  apply hbase.2
  exact catalystPoolFamilyOpen_mono (fun z => Cat z.1 z.2)
    hsub.1 (crossViableReactions_mono hsub.2 hsub.1 x) hopen

/-- All members of a fixed fresh left batch remain closed-family barriers in
the one common cavity that withholds the entire batch. -/
theorem freshLeftTargetCavityWidth_batch_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ∀ x ∈ U, x ∈ freshLeftTargetCavityWidth
        (foodLength := foodLength) Cat T P k →
      foodLength < molLength x ∧
        ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).2
          (crossViableReactions
            (crossPoolIter foodLength
              (closeTargetBlocks Cat (T ∪ U)) P k).1
            (crossPoolIter foodLength
              (closeTargetBlocks Cat (T ∪ U)) P k).2 x) := by
  classical
  intro x hxU hxfresh
  let Sx := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ {x})) P k
  let SU := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ U)) P k
  have hxclosed := freshLeftTargetCavityWidth_leaveOne_familyClosed
    Cat T P hxfresh
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ U) y r →
      closeTargetBlocks Cat (T ∪ {x}) y r := by
    intro y r h
    refine ⟨h.1, ?_⟩
    intro hr
    apply h.2
    rcases Finset.mem_union.mp hr with hrT | hrx
    · exact Finset.mem_union_left _ hrT
    · have hprod : reactionProduct r = x := Finset.mem_singleton.mp hrx
      exact Finset.mem_union_right _ (hprod.symm ▸ hxU)
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  refine ⟨hxclosed.1, ?_⟩
  intro hopen
  apply hxclosed.2
  exact catalystPoolFamilyOpen_mono (fun z => Cat z.1 z.2)
    hsub.2 (crossViableReactions_mono hsub.1 hsub.2 x) hopen

/-- Right-pool common deep-cavity batch certificate. -/
theorem freshRightTargetCavityWidth_batch_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ∀ x ∈ U, x ∈ freshRightTargetCavityWidth
        (foodLength := foodLength) Cat T P k →
      foodLength < molLength x ∧
        ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).1
          (crossViableReactions
            (crossPoolIter foodLength
              (closeTargetBlocks Cat (T ∪ U)) P k).2
            (crossPoolIter foodLength
              (closeTargetBlocks Cat (T ∪ U)) P k).1 x) := by
  classical
  intro x hxU hxfresh
  let Sx := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ {x})) P k
  let SU := crossPoolIter foodLength
    (closeTargetBlocks Cat (T ∪ U)) P k
  have hxclosed := freshRightTargetCavityWidth_leaveOne_familyClosed
    Cat T P hxfresh
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ U) y r →
      closeTargetBlocks Cat (T ∪ {x}) y r := by
    intro y r h
    refine ⟨h.1, ?_⟩
    intro hr
    apply h.2
    rcases Finset.mem_union.mp hr with hrT | hrx
    · exact Finset.mem_union_left _ hrT
    · have hprod : reactionProduct r = x := Finset.mem_singleton.mp hrx
      exact Finset.mem_union_right _ (hprod.symm ▸ hxU)
  have hsub := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) k
  refine ⟨hxclosed.1, ?_⟩
  intro hopen
  apply hxclosed.2
  exact catalystPoolFamilyOpen_mono (fun z => Cat z.1 z.2)
    hsub.1 (crossViableReactions_mono hsub.2 hsub.1 x) hopen

/-- A fresh left discrepancy from any earlier generation remains a closed
family in a common batch cavity evaluated at a later time. -/
theorem freshLeftTargetCavityWidth_prior_batch_familyClosed
    {n foodLength j k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hjk : j ≤ k) {x : Molecule n}
    (hx : x ∈ freshLeftTargetCavityWidth
      (foodLength := foodLength) Cat T P j) :
    foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2
        (crossViableReactions
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).1
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).2 x) := by
  have hbase := freshLeftTargetCavityWidth_familyClosed Cat T P hx
  have hCat : ∀ y r, closeTargetBlocks Cat (T ∪ U) y r →
      closeTargetBlocks Cat T y r := by
    intro y r h
    exact ⟨h.1, fun hrT => h.2 (Finset.mem_union_left _ hrT)⟩
  have hclose := crossPoolIter_mono (foodLength := foodLength)
    (P := P) (Q := P) hCat (Finset.Subset.rfl) (Finset.Subset.rfl) j
  have htime := crossPoolIter_mono_time (foodLength := foodLength)
    (closeTargetBlocks Cat (T ∪ U)) P hjk
  have hleft := htime.1.trans hclose.1
  have hright := htime.2.trans hclose.2
  refine ⟨hbase.1, ?_⟩
  intro hopen
  apply hbase.2
  exact catalystPoolFamilyOpen_mono (fun z => Cat z.1 z.2)
    hright (crossViableReactions_mono hleft hright x) hopen

/-- All left discrepancies that first appeared before time `k` can be charged
simultaneously in one terminal common cavity, with no generation labels. -/
theorem freshLeftTargetCavityWidth_all_prior_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hU : U ⊆ Finset.biUnion (Finset.range k) fun j =>
      freshLeftTargetCavityWidth (foodLength := foodLength) Cat T P j) :
    ∀ x ∈ U, foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).2
        (crossViableReactions
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).1
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).2 x) := by
  classical
  intro x hxU
  rcases Finset.mem_biUnion.mp (hU hxU) with ⟨j, hj, hxj⟩
  exact freshLeftTargetCavityWidth_prior_batch_familyClosed
    Cat T U P (Finset.mem_range.mp hj).le hxj

/-- Right-pool form of the all-prior-generations common-cavity certificate. -/
theorem freshRightTargetCavityWidth_all_prior_familyClosed
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T U : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hU : U ⊆ Finset.biUnion (Finset.range k) fun j =>
      freshRightTargetCavityWidth (foodLength := foodLength) Cat T P j) :
    ∀ x ∈ U, foodLength < molLength x ∧
      ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2)
        (crossPoolIter foodLength
          (closeTargetBlocks Cat (T ∪ U)) P k).1
        (crossViableReactions
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).2
          (crossPoolIter foodLength
            (closeTargetBlocks Cat (T ∪ U)) P k).1 x) := by
  have hleft := freshLeftTargetCavityWidth_all_prior_familyClosed
    Cat T U (P.2, P.1) (by
      simpa only [freshRightTargetCavityWidth_eq_left_swap] using hU)
  simpa only [crossPoolIter_swap] using hleft

/-- Every terminal left discrepancy is either held or belongs to the union of
the earlier fresh generations.  This lower-layer copy is available to the
probability module without creating an import cycle. -/
theorem leftTargetCavityWidth_subset_held_union_allFresh
    {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    leftTargetCavityWidth (foodLength := foodLength) Cat T P k ⊆
      T ∪ (Finset.range k).biUnion
        (freshLeftTargetCavityWidth (foodLength := foodLength) Cat T P) := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      intro x hx
      by_cases hprev : x ∈ leftTargetCavityWidth
          (foodLength := foodLength) Cat T P k ∪ T
      · rcases Finset.mem_union.mp hprev with hxold | hxT
        · rcases Finset.mem_union.mp (ih hxold) with hxT | hxgen
          · exact Finset.mem_union_left _ hxT
          · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxgen
            exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
              ⟨j, Finset.mem_range.mpr (by
                have := Finset.mem_range.mp hj
                omega), hxj⟩)
        · exact Finset.mem_union_left _ hxT
      · have hxfresh : x ∈ freshLeftTargetCavityWidth
            (foodLength := foodLength) Cat T P k :=
          Finset.mem_sdiff.mpr ⟨hx, hprev⟩
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨k, Finset.mem_range.mpr (by omega), hxfresh⟩)

end HordijkSteelThreshold

import proofs.HordijkSteelThreshold.TwoPoolCoreAdapter
import proofs.HordijkSteelThreshold.FamilyOpenProbability

namespace HordijkSteelThreshold

open MeasureTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A molecule on the left survives one synchronous pruning step when it is
temporary food or has a viable split catalyzed from the current right pool. -/
def crossLeftSurvives {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A B : Finset (Molecule n)) (x : Molecule n) : Prop :=
  molLength x ≤ foodLength ∨
    ∃ r : Reaction n,
      reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
        reactionRight r ∈ A ∪ B ∧ ∃ y ∈ B, Cat y r

/-- A one-step survival query for `x` reads only catalysis coordinates whose
reaction product is `x`. This is the leave-one-target locality needed to
separate a target block from the pruning state used to test it. -/
theorem crossLeftSurvives_congr_targetBlock {n foodLength : Nat}
    {Cat Cat' : Catalysis (Molecule n) (Reaction n)}
    (A B : Finset (Molecule n)) (x : Molecule n)
    (hCat : ∀ y r, reactionProduct r = x → (Cat y r ↔ Cat' y r)) :
    crossLeftSurvives foodLength Cat A B x ↔
      crossLeftSurvives foodLength Cat' A B x := by
  constructor
  · rintro (hfood | ⟨r, hrx, hl, hr, y, hy, hcy⟩)
    · exact Or.inl hfood
    · exact Or.inr ⟨r, hrx, hl, hr, y, hy, (hCat y r hrx).mp hcy⟩
  · rintro (hfood | ⟨r, hrx, hl, hr, y, hy, hcy⟩)
    · exact Or.inl hfood
    · exact Or.inr ⟨r, hrx, hl, hr, y, hy, (hCat y r hrx).mpr hcy⟩

theorem crossLeftSurvives_mono {n foodLength : Nat}
    {Cat Cat' : Catalysis (Molecule n) (Reaction n)}
    {A A' B B' : Finset (Molecule n)}
    (hCat : ∀ y r, Cat y r → Cat' y r) (hA : A ⊆ A') (hB : B ⊆ B')
    {x : Molecule n}
    (hx : crossLeftSurvives foodLength Cat A B x) :
    crossLeftSurvives foodLength Cat' A' B' x := by
  rcases hx with hfood | ⟨r, hrx, hl, hr, y, hy, hcy⟩
  · exact Or.inl hfood
  · refine Or.inr ⟨r, hrx, ?_, ?_, y, hB hy, hCat y r hcy⟩
    · rcases Finset.mem_union.mp hl with hl | hl
      · exact Finset.mem_union_left _ (hA hl)
      · exact Finset.mem_union_right _ (hB hl)
    · rcases Finset.mem_union.mp hr with hr | hr
      · exact Finset.mem_union_left _ (hA hr)
      · exact Finset.mem_union_right _ (hB hr)

/-- Close every catalysis coordinate whose reaction product lies in `T`. -/
def closeTargetBlocks {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) : Catalysis (Molecule n) (Reaction n) :=
  fun y r => Cat y r ∧ reactionProduct r ∉ T

/-- Open every catalysis coordinate whose reaction product lies in `T`. -/
def openTargetBlocks {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T : Finset (Molecule n)) : Catalysis (Molecule n) (Reaction n) :=
  fun y r => Cat y r ∨ reactionProduct r ∈ T

theorem closeTargetBlocks_le {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n)) (T : Finset (Molecule n)) :
    ∀ y r, closeTargetBlocks Cat T y r → Cat y r := by
  intro y r h
  exact h.1

theorem le_openTargetBlocks {n : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n)) (T : Finset (Molecule n)) :
    ∀ y r, Cat y r → openTargetBlocks Cat T y r := by
  intro y r h
  exact Or.inl h

/-- Away from `T`, closing or opening the target blocks does not alter a
one-step survival query when the input pools are held fixed. -/
theorem crossLeftSurvives_targetBlock_sandwich_eq {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (T A B : Finset (Molecule n)) {x : Molecule n} (hxT : x ∉ T) :
    (crossLeftSurvives foodLength (closeTargetBlocks Cat T) A B x ↔
      crossLeftSurvives foodLength Cat A B x) ∧
    (crossLeftSurvives foodLength Cat A B x ↔
      crossLeftSurvives foodLength (openTargetBlocks Cat T) A B x) := by
  have hclose : ∀ y r, reactionProduct r = x →
      (closeTargetBlocks Cat T y r ↔ Cat y r) := by
    intro y r hr
    simp [closeTargetBlocks, hr, hxT]
  have hopen : ∀ y r, reactionProduct r = x →
      (Cat y r ↔ openTargetBlocks Cat T y r) := by
    intro y r hr
    simp [openTargetBlocks, hr, hxT]
  exact ⟨(crossLeftSurvives_congr_targetBlock A B x hclose),
    crossLeftSurvives_congr_targetBlock A B x hopen⟩

/-- Reactions that are factor-viable for one target in the current pair. -/
noncomputable def crossViableReactions {n : Nat}
    (A B : Finset (Molecule n)) (x : Molecule n) : Finset (Reaction n) := by
  classical
  exact Finset.univ.filter fun r =>
    reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
      reactionRight r ∈ A ∪ B

@[simp] theorem mem_crossViableReactions {n : Nat}
    (A B : Finset (Molecule n)) (x : Molecule n) (r : Reaction n) :
    r ∈ crossViableReactions A B x ↔
      reactionProduct r = x ∧ reactionLeft r ∈ A ∪ B ∧
        reactionRight r ∈ A ∪ B := by
  classical
  simp [crossViableReactions]

/-- The concrete reaction producing `x` at one of its split positions. -/
def reactionAtSplit {n : Nat} (x : Molecule n) (j : Fin x.1.val) :
    Reaction n :=
  ⟨x.1, x.2, j⟩

theorem reactionAtSplit_injective {n : Nat} (x : Molecule n) :
    Function.Injective (reactionAtSplit x) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun r : Reaction n => r.2.2.val) hij

/-- Split positions whose two concrete factors survive in the current pair. -/
noncomputable def crossViableSplitPositions {n : Nat}
    (A B : Finset (Molecule n)) (x : Molecule n) : Finset (Fin x.1.val) := by
  classical
  exact Finset.univ.filter fun j =>
    reactionLeft (reactionAtSplit x j) ∈ A ∪ B ∧
      reactionRight (reactionAtSplit x j) ∈ A ∪ B

/-- Split positions of a fixed target at which `u` is one of the two factors. -/
noncomputable def factorSensitiveSplitPositions {n : Nat}
    (u x : Molecule n) : Finset (Fin x.1.val) := by
  classical
  exact Finset.univ.filter fun j =>
    reactionLeft (reactionAtSplit x j) = u ∨
      reactionRight (reactionAtSplit x j) = u

/-- A fixed molecule can occur in a fixed product at at most one prefix split
and at most one suffix split. -/
theorem card_factorSensitiveSplitPositions_le_two {n : Nat}
    (u x : Molecule n) :
    (factorSensitiveSplitPositions u x).card ≤ 2 := by
  classical
  let L : Finset (Fin x.1.val) := Finset.univ.filter fun j =>
    reactionLeft (reactionAtSplit x j) = u
  let R : Finset (Fin x.1.val) := Finset.univ.filter fun j =>
    reactionRight (reactionAtSplit x j) = u
  have hL : L.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    have hiu := (Finset.mem_filter.mp hi).2
    have hju := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    have hlen := congrArg molLength (hiu.trans hju.symm)
    simpa [reactionAtSplit, reactionLeftLength] using hlen)
  have hR : R.card ≤ 1 := Finset.card_le_one.mpr (by
    intro i hi j hj
    have hiu := (Finset.mem_filter.mp hi).2
    have hju := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    have hlen := congrArg molLength (hiu.trans hju.symm)
    simp [reactionAtSplit, reactionRightLength] at hlen
    omega)
  have hset : factorSensitiveSplitPositions u x = L ∪ R := by
    ext j
    simp [factorSensitiveSplitPositions, L, R, and_or_left]
  rw [hset]
  exact (Finset.card_union_le L R).trans (by omega)

/-- Every viable split position supplies a distinct viable reaction identity. -/
theorem card_crossViableSplitPositions_le_reactions {n : Nat}
    (A B : Finset (Molecule n)) (x : Molecule n) :
    (crossViableSplitPositions A B x).card ≤
      (crossViableReactions A B x).card := by
  classical
  let f : Fin x.1.val → Reaction n := reactionAtSplit x
  have himage : (crossViableSplitPositions A B x).image f ⊆
      crossViableReactions A B x := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
    have hv := (Finset.mem_filter.mp hj).2
    apply (mem_crossViableReactions A B x (reactionAtSplit x j)).mpr
    exact ⟨rfl, hv.1, hv.2⟩
  calc
    (crossViableSplitPositions A B x).card =
        ((crossViableSplitPositions A B x).image f).card := by
      symm
      exact Finset.card_image_iff.mpr (reactionAtSplit_injective x).injOn
    _ ≤ (crossViableReactions A B x).card := Finset.card_le_card himage

theorem crossViableReactions_disjoint {n : Nat}
    (A B : Finset (Molecule n)) {x y : Molecule n} (hxy : x ≠ y) :
    Disjoint (crossViableReactions A B x) (crossViableReactions A B y) := by
  rw [Finset.disjoint_left]
  intro r hrx hry
  have hxprod := (mem_crossViableReactions A B x r).mp hrx |>.1
  have hyprod := (mem_crossViableReactions A B y r).mp hry |>.1
  exact hxy (hxprod.symm.trans hyprod)

/-- Distinct targets have disjoint reaction identities, so a uniform lower
bound on viable splits adds exactly across a barrier target set. -/
theorem card_biUnion_crossViableReactions_ge {n d : Nat}
    (A B T : Finset (Molecule n))
    (hcard : ∀ x ∈ T, d ≤ (crossViableReactions A B x).card) :
    d * T.card ≤ (T.biUnion (crossViableReactions A B)).card := by
  classical
  have hpair : (T : Set (Molecule n)).PairwiseDisjoint
      (crossViableReactions A B) := by
    intro x hx y hy hxy
    exact crossViableReactions_disjoint A B hxy
  rw [Finset.card_biUnion hpair]
  calc
    d * T.card = ∑ x ∈ T, d := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ T, (crossViableReactions A B x).card := by
      exact Finset.sum_le_sum fun x hx => hcard x hx

/-- One simultaneous cross-pool pruning step.  Membership can only be lost;
the initial assignment of temporary-food molecules to the two pools is kept. -/
noncomputable def crossPoolStep {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    Finset (Molecule n) × Finset (Molecule n) := by
  classical
  exact (P.1.filter (crossLeftSurvives foodLength Cat P.1 P.2),
    P.2.filter (crossLeftSurvives foodLength Cat P.2 P.1))

/-- One synchronous pruning step is monotone in catalysis and in both input
pools. -/
theorem crossPoolStep_mono {n foodLength : Nat}
    {Cat Cat' : Catalysis (Molecule n) (Reaction n)}
    {P Q : Finset (Molecule n) × Finset (Molecule n)}
    (hCat : ∀ y r, Cat y r → Cat' y r)
    (hleft : P.1 ⊆ Q.1) (hright : P.2 ⊆ Q.2) :
    (crossPoolStep foodLength Cat P).1 ⊆
        (crossPoolStep foodLength Cat' Q).1 ∧
      (crossPoolStep foodLength Cat P).2 ⊆
        (crossPoolStep foodLength Cat' Q).2 := by
  classical
  constructor
  · intro x hx
    rw [crossPoolStep] at hx ⊢
    have hmem := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hleft hmem.1,
      crossLeftSurvives_mono hCat hleft hright hmem.2⟩
  · intro x hx
    rw [crossPoolStep] at hx ⊢
    have hmem := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hright hmem.1,
      crossLeftSurvives_mono hCat hright hleft hmem.2⟩

theorem crossPoolStep_left_subset {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    (crossPoolStep foodLength Cat P).1 ⊆ P.1 := by
  classical
  intro x hx
  change x ∈ P.1.filter (crossLeftSurvives foodLength Cat P.1 P.2) at hx
  exact (Finset.mem_filter.mp hx).1

theorem crossPoolStep_right_subset {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    (crossPoolStep foodLength Cat P).2 ⊆ P.2 := by
  classical
  intro x hx
  change x ∈ P.2.filter (crossLeftSurvives foodLength Cat P.2 P.1) at hx
  exact (Finset.mem_filter.mp hx).1

/-- Exact one-step barrier certificate on the left: a currently assigned
target is removed precisely when it is nonfood and its whole viable reaction
family is closed against the current right catalyst pool. -/
theorem not_mem_crossPoolStep_left_iff {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A B : Finset (Molecule n)) {x : Molecule n} (hx : x ∈ A) :
    x ∉ (crossPoolStep foodLength Cat (A, B)).1 ↔
      foodLength < molLength x ∧
        ¬catalystPoolFamilyOpen (fun z => Cat z.1 z.2) B
          (crossViableReactions A B x) := by
  classical
  change x ∉ A.filter (crossLeftSurvives foodLength Cat A B) ↔ _
  constructor
  · intro hnot
    have hnotSurvives : ¬crossLeftSurvives foodLength Cat A B x := by
      intro hsurvives
      exact hnot (Finset.mem_filter.mpr ⟨hx, hsurvives⟩)
    have hlen : foodLength < molLength x := by
      exact Nat.lt_of_not_ge (fun hlow => hnotSurvives (Or.inl hlow))
    refine ⟨hlen, ?_⟩
    rintro ⟨r, hr, y, hy, hcat⟩
    apply hnotSurvives
    right
    have hrv := (mem_crossViableReactions A B x r).mp hr
    exact ⟨r, hrv.1, hrv.2.1, hrv.2.2, y, hy, hcat⟩
  · rintro ⟨hlen, hclosed⟩ hxstep
    have hsurvives := (Finset.mem_filter.mp hxstep).2
    rcases hsurvives with hlow | ⟨r, hprod, hleft, hright, y, hy, hcat⟩
    · exact (Nat.not_lt_of_ge hlow hlen).elim
    · apply hclosed
      exact ⟨r, (mem_crossViableReactions A B x r).mpr
        ⟨hprod, hleft, hright⟩, y, hy, hcat⟩

/-- Exact probability of a fixed one-step left barrier.  The state `(A,B)`
and proposed removed target set `T` are fixed before the catalysis block is
exposed; overlapping viable reaction families are charged through their union. -/
theorem measure_fixed_crossPoolStep_left_barrier {n foodLength : Nat}
    (lambda : ℝ) (A B T : Finset (Molecule n))
    (hTA : T ⊆ A) (hlen : ∀ x ∈ T, foodLength < molLength x) :
    ambientPiMeasure n lambda
        {ω | ∀ x ∈ T,
          x ∉ (crossPoolStep foodLength (fun y r => ω (y, r)) (A, B)).1} =
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (B.card * (T.biUnion (crossViableReactions A B)).card) := by
  classical
  rw [show {ω | ∀ x ∈ T,
        x ∉ (crossPoolStep foodLength (fun y r => ω (y, r)) (A, B)).1} =
      {ω | catalystPoolFamiliesClosed ω B T (crossViableReactions A B)} by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h x hx
          exact (not_mem_crossPoolStep_left_iff
            (fun y r => ω (y, r)) A B (hTA hx)).mp (h x hx) |>.2
        · intro h x hx
          exact (not_mem_crossPoolStep_left_iff
            (fun y r => ω (y, r)) A B (hTA hx)).mpr
              ⟨hlen x hx, h x hx⟩]
  exact measure_catalystPoolFamiliesClosed lambda B T
    (crossViableReactions A B)

/-- Energy bound for a fixed barrier: if every removed target has at least
`d` distinct viable reactions, its probability is at most the closed
coordinate probability raised to `|B| d |T|`. -/
theorem measure_fixed_crossPoolStep_left_barrier_le {n foodLength d : Nat}
    (lambda : ℝ) (A B T : Finset (Molecule n))
    (hTA : T ⊆ A) (hlen : ∀ x ∈ T, foodLength < molLength x)
    (hcard : ∀ x ∈ T, d ≤ (crossViableReactions A B x).card) :
    ambientPiMeasure n lambda
        {ω | ∀ x ∈ T,
          x ∉ (crossPoolStep foodLength (fun y r => ω (y, r)) (A, B)).1} ≤
      (toNNReal (σ (catalysisP n lambda)) : ENNReal) ^
        (B.card * (d * T.card)) := by
  rw [measure_fixed_crossPoolStep_left_barrier lambda A B T hTA hlen]
  apply pow_le_pow_right_of_le_one'
  · exact_mod_cast (σ (catalysisP n lambda)).2.2
  · exact Nat.mul_le_mul_left B.card
      (card_biUnion_crossViableReactions_ge A B T hcard)

/-- Fixed points of synchronous pruning are exactly cross-supported pools,
provided the current pair still contains the temporary food. -/
theorem crossPoolStep_eq_self_iff {n foodLength : Nat}
    {Cat : Catalysis (Molecule n) (Reaction n)}
    {A B : Finset (Molecule n)}
    (hfood : binaryFood n foodLength ⊆ A ∪ B) :
    crossPoolStep foodLength Cat (A, B) = (A, B) ↔
      IsCrossSupportedMoleculePools foodLength Cat A B := by
  classical
  constructor
  · intro hfix
    have hleft : (crossPoolStep foodLength Cat (A, B)).1 = A :=
      congrArg Prod.fst hfix
    have hright : (crossPoolStep foodLength Cat (A, B)).2 = B :=
      congrArg Prod.snd hfix
    refine ⟨hfood, ?_, ?_⟩
    · intro x hx hlen
      have hxstep : x ∈ (crossPoolStep foodLength Cat (A, B)).1 :=
        hleft.symm ▸ hx
      have hsurvive := (Finset.mem_filter.mp hxstep).2
      rcases hsurvive with hlow | hsupp
      · exact (Nat.not_lt_of_ge hlow hlen).elim
      · simpa [Finset.union_comm] using hsupp
    · intro x hx hlen
      have hxstep : x ∈ (crossPoolStep foodLength Cat (A, B)).2 :=
        hright.symm ▸ hx
      have hsurvive := (Finset.mem_filter.mp hxstep).2
      rcases hsurvive with hlow | hsupp
      · exact (Nat.not_lt_of_ge hlow hlen).elim
      · simpa [Finset.union_comm] using hsupp
  · intro hcross
    apply Prod.ext
    · apply Finset.Subset.antisymm
      · exact crossPoolStep_left_subset Cat (A, B)
      · intro x hx
        apply Finset.mem_filter.mpr
        refine ⟨hx, ?_⟩
        by_cases hlen : foodLength < molLength x
        · exact Or.inr (hcross.2.1 x hx hlen)
        · exact Or.inl (Nat.le_of_not_gt hlen)
    · apply Finset.Subset.antisymm
      · exact crossPoolStep_right_subset Cat (A, B)
      · intro x hx
        apply Finset.mem_filter.mpr
        refine ⟨hx, ?_⟩
        by_cases hlen : foodLength < molLength x
        · exact Or.inr (by
            simpa [Finset.union_comm] using hcross.2.2 x hx hlen)
        · exact Or.inl (Nat.le_of_not_gt hlen)

/-- Synchronous pruning history from an arbitrary initial pair. -/
noncomputable def crossPoolIter {n : Nat} (foodLength : Nat)
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) : Nat →
    Finset (Molecule n) × Finset (Molecule n)
  | 0 => P
  | k + 1 => crossPoolStep foodLength Cat (crossPoolIter foodLength Cat P k)

/-- The leave-out and forced-in pruning histories remain ordered at every
round. -/
theorem crossPoolIter_mono {n foodLength : Nat}
    {Cat Cat' : Catalysis (Molecule n) (Reaction n)}
    {P Q : Finset (Molecule n) × Finset (Molecule n)}
    (hCat : ∀ y r, Cat y r → Cat' y r)
    (hleft : P.1 ⊆ Q.1) (hright : P.2 ⊆ Q.2) (k : Nat) :
    (crossPoolIter foodLength Cat P k).1 ⊆
        (crossPoolIter foodLength Cat' Q k).1 ∧
      (crossPoolIter foodLength Cat P k).2 ⊆
        (crossPoolIter foodLength Cat' Q k).2 := by
  induction k with
  | zero => exact ⟨hleft, hright⟩
  | succ k ih =>
      exact crossPoolStep_mono hCat ih.1 ih.2

theorem crossPoolIter_succ_subset {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :
    (crossPoolIter foodLength Cat P (k + 1)).1 ⊆
        (crossPoolIter foodLength Cat P k).1 ∧
      (crossPoolIter foodLength Cat P (k + 1)).2 ⊆
        (crossPoolIter foodLength Cat P k).2 := by
  exact ⟨crossPoolStep_left_subset Cat _, crossPoolStep_right_subset Cat _⟩

theorem crossPoolIter_step_start {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) (k : Nat) :
    crossPoolIter foodLength Cat P (k + 1) =
      crossPoolIter foodLength Cat (crossPoolStep foodLength Cat P) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change crossPoolStep foodLength Cat
          (crossPoolIter foodLength Cat P (k + 1)) =
        crossPoolStep foodLength Cat
          (crossPoolIter foodLength Cat
            (crossPoolStep foodLength Cat P) k)
      exact congrArg (crossPoolStep foodLength Cat) ih

/-- Every finite synchronous history reaches a fixed point before more
iterations have elapsed than there were initially assigned molecules. -/
theorem exists_crossPoolIter_fixed {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    ∃ k ≤ P.1.card + P.2.card,
      crossPoolIter foodLength Cat P (k + 1) =
        crossPoolIter foodLength Cat P k := by
  classical
  by_cases hfix : crossPoolStep foodLength Cat P = P
  · exact ⟨0, by omega, hfix⟩
  · let Q := crossPoolStep foodLength Cat P
    have hsub1 : Q.1 ⊆ P.1 := crossPoolStep_left_subset Cat P
    have hsub2 : Q.2 ⊆ P.2 := crossPoolStep_right_subset Cat P
    have hlt : Q.1.card + Q.2.card < P.1.card + P.2.card := by
      have hc1 := Finset.card_le_card hsub1
      have hc2 := Finset.card_le_card hsub2
      apply Nat.lt_of_le_of_ne (by omega)
      intro heq
      have hc1eq : Q.1.card = P.1.card := by omega
      have hc2eq : Q.2.card = P.2.card := by omega
      have hq1 : Q.1 = P.1 :=
        Finset.eq_of_subset_of_card_le hsub1 (by omega)
      have hq2 : Q.2 = P.2 :=
        Finset.eq_of_subset_of_card_le hsub2 (by omega)
      exact hfix (Prod.ext hq1 hq2)
    obtain ⟨k, hk, hstable⟩ :=
      exists_crossPoolIter_fixed (foodLength := foodLength) Cat Q
    refine ⟨k + 1, by omega, ?_⟩
    calc
      crossPoolIter foodLength Cat P ((k + 1) + 1) =
          crossPoolIter foodLength Cat Q (k + 1) :=
        crossPoolIter_step_start Cat P (k + 1)
      _ = crossPoolIter foodLength Cat Q k := hstable
      _ = crossPoolIter foodLength Cat P (k + 1) :=
        (crossPoolIter_step_start Cat P k).symm
termination_by P.1.card + P.2.card

/-- Once a pruning iterate is fixed, every later iterate is the same state. -/
theorem crossPoolIter_add_eq_of_fixed {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n))
    (hfix : crossPoolIter foodLength Cat P (k + 1) =
      crossPoolIter foodLength Cat P k) (j : Nat) :
    crossPoolIter foodLength Cat P (k + j) =
      crossPoolIter foodLength Cat P k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.add_succ]
      change crossPoolStep foodLength Cat
          (crossPoolIter foodLength Cat P (k + j)) = _
      rw [ih]
      exact hfix

/-- The crude initial-cardinality bound is a canonical deterministic
stabilization time, avoiding an existential stopping-time choice. -/
theorem crossPoolIter_fixed_at_card_bound {n foodLength : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (P : Finset (Molecule n) × Finset (Molecule n)) :
    crossPoolIter foodLength Cat P (P.1.card + P.2.card + 1) =
      crossPoolIter foodLength Cat P (P.1.card + P.2.card) := by
  obtain ⟨k, hk, hfix⟩ := exists_crossPoolIter_fixed Cat P
  let N := P.1.card + P.2.card
  have hNk : N = k + (N - k) := (Nat.add_sub_of_le hk).symm
  have hN := crossPoolIter_add_eq_of_fixed Cat P hfix (N - k)
  rw [← hNk] at hN
  change crossPoolStep foodLength Cat
      (crossPoolIter foodLength Cat P N) =
    crossPoolIter foodLength Cat P N
  rw [hN]
  exact hfix

/-- Diagonal initial pools remain diagonal under synchronous cross pruning. -/
theorem crossPoolIter_diagonal {n foodLength k : Nat}
    (Cat : Catalysis (Molecule n) (Reaction n))
    (A : Finset (Molecule n)) :
    (crossPoolIter foodLength Cat (A, A) k).1 =
      (crossPoolIter foodLength Cat (A, A) k).2 := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
      change
        ((crossPoolIter foodLength Cat (A, A) k).1.filter
          (crossLeftSurvives foodLength Cat
            (crossPoolIter foodLength Cat (A, A) k).1
            (crossPoolIter foodLength Cat (A, A) k).2)) =
        ((crossPoolIter foodLength Cat (A, A) k).2.filter
          (crossLeftSurvives foodLength Cat
            (crossPoolIter foodLength Cat (A, A) k).2
            (crossPoolIter foodLength Cat (A, A) k).1))
      rw [ih]

end HordijkSteelThreshold

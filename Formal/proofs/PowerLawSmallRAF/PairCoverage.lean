import proofs.PowerLawSmallRAF.FirstMomentProfile

namespace PowerLawSmallRAF

variable {R : Type*} [DecidableEq R]

/-- The three disjoint Venn cells of an ordered pair of finite supports,
assembled as a type equivalent to their union. -/
noncomputable def pairCellDecomposition (S T : Finset R) :
    ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) ≃
      ↥(((S \ T) ∪ (S ∩ T)) ∪ (T \ S)) := by
  classical
  have hleft : Disjoint (S \ T) (S ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hx hxboth
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx hxboth
    exact hx.2 hxboth.2
  have hright : Disjoint ((S \ T) ∪ (S ∩ T)) (T \ S) := by
    rw [Finset.disjoint_left]
    intro x hx hxright
    rcases Finset.mem_union.mp hx with hxleft | hxboth
    · simp only [Finset.mem_sdiff] at hxleft hxright
      exact hxleft.2 hxright.1
    · simp only [Finset.mem_inter, Finset.mem_sdiff] at hxboth hxright
      exact hxright.2 hxboth.1
  let e :=
    ((Equiv.Finset.union (S \ T) (S ∩ T) hleft).sumCongr
      (Equiv.refl ↥(T \ S))).trans
        (Equiv.Finset.union ((S \ T) ∪ (S ∩ T)) (T \ S) hright)
  exact e

@[simp]
theorem pairCellDecomposition_left
    (S T : Finset R) (x : ↥(S \ T)) :
    (pairCellDecomposition S T (Sum.inl (Sum.inl x)) : R) = x := by
  classical
  simp [pairCellDecomposition]

@[simp]
theorem pairCellDecomposition_both
    (S T : Finset R) (x : ↥(S ∩ T)) :
    (pairCellDecomposition S T (Sum.inl (Sum.inr x)) : R) = x := by
  classical
  simp [pairCellDecomposition]

@[simp]
theorem pairCellDecomposition_right
    (S T : Finset R) (x : ↥(T \ S)) :
    (pairCellDecomposition S T (Sum.inr x) : R) = x := by
  classical
  simp [pairCellDecomposition]

/-- Equal left size, right size, and overlap produce one ambient permutation
that transports both supports simultaneously. -/
theorem exists_pairSupportPerm
    (S T S' T' : Finset R)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card) :
    ∃ σ : Equiv.Perm R,
      S.map σ.toEmbedding = S' ∧ T.map σ.toEmbedding = T' := by
  classical
  have hA : (S \ T).card = (S' \ T').card := by
    have hleft := Finset.card_sdiff_add_card_inter S T
    have hright := Finset.card_sdiff_add_card_inter S' T'
    omega
  have hB : (T \ S).card = (T' \ S').card := by
    have hleft := Finset.card_sdiff_add_card_inter T S
    have hright := Finset.card_sdiff_add_card_inter T' S'
    have hI' : (T ∩ S).card = (T' ∩ S').card := by
      simpa [Finset.inter_comm] using hI
    omega
  let eA : ↥(S \ T) ≃ ↥(S' \ T') := Finset.equivOfCardEq hA
  let eI : ↥(S ∩ T) ≃ ↥(S' ∩ T') := Finset.equivOfCardEq hI
  let eB : ↥(T \ S) ≃ ↥(T' \ S') := Finset.equivOfCardEq hB
  let eCells := (eA.sumCongr eI).sumCongr eB
  let f : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) → R :=
    fun z => pairCellDecomposition S T z
  let g : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) → R :=
    fun z => pairCellDecomposition S' T' (eCells z)
  have hf : Function.Injective f := by
    intro x y hxy
    apply (pairCellDecomposition S T).injective
    exact Subtype.ext hxy
  have hg : Function.Injective g := by
    intro x y hxy
    apply eCells.injective
    apply (pairCellDecomposition S' T').injective
    exact Subtype.ext hxy
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hmapS : S.map σ.toEmbedding ⊆ S' := by
    intro y hy
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_map.mp hy
    by_cases hxT : x ∈ T
    · let z : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) :=
        Sum.inl (Sum.inr ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩)
      have hz := hσ z
      change σ x = ((eI ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩ :
        ↥(S' ∩ T')) : R) at hz
      change σ x ∈ S'
      rw [hz]
      exact Finset.mem_inter.mp
        (eI ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩).2 |>.1
    · let z : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) :=
        Sum.inl (Sum.inl ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxT⟩⟩)
      have hz := hσ z
      change σ x = ((eA ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxT⟩⟩ :
        ↥(S' \ T')) : R) at hz
      change σ x ∈ S'
      rw [hz]
      exact Finset.mem_sdiff.mp
        (eA ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxT⟩⟩).2 |>.1
  have hmapT : T.map σ.toEmbedding ⊆ T' := by
    intro y hy
    obtain ⟨x, hxT, rfl⟩ := Finset.mem_map.mp hy
    by_cases hxS : x ∈ S
    · let z : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) :=
        Sum.inl (Sum.inr ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩)
      have hz := hσ z
      change σ x = ((eI ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩ :
        ↥(S' ∩ T')) : R) at hz
      change σ x ∈ T'
      rw [hz]
      exact Finset.mem_inter.mp
        (eI ⟨x, Finset.mem_inter.mpr ⟨hxS, hxT⟩⟩).2 |>.2
    · let z : ((↥(S \ T) ⊕ ↥(S ∩ T)) ⊕ ↥(T \ S)) :=
        Sum.inr ⟨x, Finset.mem_sdiff.mpr ⟨hxT, hxS⟩⟩
      have hz := hσ z
      change σ x = ((eB ⟨x, Finset.mem_sdiff.mpr ⟨hxT, hxS⟩⟩ :
        ↥(T' \ S')) : R) at hz
      change σ x ∈ T'
      rw [hz]
      exact Finset.mem_sdiff.mp
        (eB ⟨x, Finset.mem_sdiff.mpr ⟨hxT, hxS⟩⟩).2 |>.1
  refine ⟨σ, Finset.eq_of_subset_of_card_le hmapS ?_,
    Finset.eq_of_subset_of_card_le hmapT ?_⟩
  · simp [hS]
  · simp [hT]

structure PairOverlapCoordinates where
  leftSize : Nat
  rightSize : Nat
  supportOverlap : Nat
  leftClosureSize : Nat
  rightClosureSize : Nat
  closureOverlap : Nat

def pairSubsetKey (J K : Finset R) : Nat × Nat × Nat :=
  (J.card, K.card, (J ∩ K).card)

def pairSubsetMultiplicity (S T : Finset R) (key : Nat × Nat × Nat) : Nat :=
  ((S.powerset.product T.powerset).filter fun pair =>
    pairSubsetKey pair.1 pair.2 = key).card

/-- A permutation carrying each support to its target transports the complete
subset-pair multiplicity table. -/
theorem pairSubsetMultiplicity_eq_of_perm
    (S T S' T' : Finset R) (σ : Equiv.Perm R)
    (hS : S.map σ.toEmbedding = S')
    (hT : T.map σ.toEmbedding = T') (key : Nat × Nat × Nat) :
    pairSubsetMultiplicity S T key = pairSubsetMultiplicity S' T' key := by
  classical
  rw [pairSubsetMultiplicity, pairSubsetMultiplicity]
  let ePair := σ.finsetCongr.prodCongr σ.finsetCongr
  apply Finset.card_equiv ePair
  intro pair
  simp only [Finset.mem_filter]
  dsimp [ePair]
  rw [Finset.mem_product, Finset.mem_product]
  simp only [Finset.mem_powerset]
  change ((pair.1 ⊆ S ∧ pair.2 ⊆ T) ∧
      pairSubsetKey pair.1 pair.2 = key) ↔
    ((pair.1.map σ.toEmbedding ⊆ S' ∧
        pair.2.map σ.toEmbedding ⊆ T') ∧
      pairSubsetKey (pair.1.map σ.toEmbedding)
        (pair.2.map σ.toEmbedding) = key)
  have hleft : pair.1.map σ.toEmbedding ⊆ S' ↔ pair.1 ⊆ S := by
    rw [← hS, Finset.map_subset_map]
  have hright : pair.2.map σ.toEmbedding ⊆ T' ↔ pair.2 ⊆ T := by
    rw [← hT, Finset.map_subset_map]
  rw [hleft, hright]
  simp only [pairSubsetKey, Finset.card_map]
  rw [← Finset.map_inter]
  simp

/-- The multiplicity table depends only on the three Venn coordinates of the
ordered support pair. -/
theorem pairSubsetMultiplicity_eq_of_card_inter
    (S T S' T' : Finset R)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card) (key : Nat × Nat × Nat) :
    pairSubsetMultiplicity S T key = pairSubsetMultiplicity S' T' key := by
  obtain ⟨σ, hmapS, hmapT⟩ := exists_pairSupportPerm S T S' T' hS hT hI
  exact pairSubsetMultiplicity_eq_of_perm S T S' T' σ hmapS hmapT key

def pairKeyRange (S T : Finset R) : Finset (Nat × Nat × Nat) :=
  (Finset.range (S.card + 1)).product
    ((Finset.range (T.card + 1)).product
      (Finset.range ((S ∩ T).card + 1)))

noncomputable def pairCoverageTerm (u : Nat → ℝ) (q q' v : Nat)
    (key : Nat × Nat × Nat) : ℝ :=
  (-1 : ℝ) ^ (key.1 + key.2.1) *
    u key.1 ^ (q - v) * u key.2.1 ^ (q' - v) *
      u (key.1 + key.2.1 - key.2.2) ^ v

noncomputable def pairCoverageKernel (u : Nat → ℝ)
    (S T : Finset R) (q q' v : Nat) : ℝ :=
  ∑ pair ∈ S.powerset.product T.powerset,
    (-1 : ℝ) ^ (pair.1.card + pair.2.card) *
      u pair.1.card ^ (q - v) * u pair.2.card ^ (q' - v) *
        u (pair.1 ∪ pair.2).card ^ v

theorem card_union_eq_pairSubsetKey (J K : Finset R) :
    (J ∪ K).card = J.card + K.card - (J ∩ K).card := by
  have hcard := Finset.card_union_add_card_inter J K
  omega

/-- The exact joint kernel collapses to the multiplicity table of the three
subset coordinates `(card J, card K, card (J ∩ K))`. -/
theorem pairCoverageKernel_eq_multiplicitySum
    (u : Nat → ℝ) (S T : Finset R) (q q' v : Nat) :
    pairCoverageKernel u S T q q' v =
      ∑ key ∈ (S.powerset.product T.powerset).image
          (fun pair => pairSubsetKey pair.1 pair.2),
        (pairSubsetMultiplicity S T key : ℝ) *
          pairCoverageTerm u q q' v key := by
  rw [pairCoverageKernel]
  let pairs := S.powerset.product T.powerset
  let keyOf : Finset R × Finset R → Nat × Nat × Nat :=
    fun pair => pairSubsetKey pair.1 pair.2
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := pairs) (t := pairs.image keyOf) (g := keyOf)
    (fun pair hpair => Finset.mem_image_of_mem keyOf hpair)
    (fun pair => (-1 : ℝ) ^ (pair.1.card + pair.2.card) *
      u pair.1.card ^ (q - v) * u pair.2.card ^ (q' - v) *
        u (pair.1 ∪ pair.2).card ^ v)]
  apply Finset.sum_congr rfl
  intro key _hkey
  rw [pairSubsetMultiplicity]
  calc
    (∑ pair ∈ pairs with keyOf pair = key,
        (-1 : ℝ) ^ (pair.1.card + pair.2.card) *
          u pair.1.card ^ (q - v) * u pair.2.card ^ (q' - v) *
            u (pair.1 ∪ pair.2).card ^ v) =
        ∑ _pair ∈ pairs with keyOf _pair = key,
          pairCoverageTerm u q q' v key := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hkey := (Finset.mem_filter.mp hpair).2
      rw [← hkey]
      simp only [keyOf, pairSubsetKey, pairCoverageTerm]
      rw [card_union_eq_pairSubsetKey]
    _ = ((pairs.filter fun pair => keyOf pair = key).card : ℝ) *
        pairCoverageTerm u q q' v key := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Canonically bounded version of the multiplicity-table kernel. -/
theorem pairCoverageKernel_eq_keyRangeSum
    (u : Nat → ℝ) (S T : Finset R) (q q' v : Nat) :
    pairCoverageKernel u S T q q' v =
      ∑ key ∈ pairKeyRange S T,
        (pairSubsetMultiplicity S T key : ℝ) *
          pairCoverageTerm u q q' v key := by
  rw [pairCoverageKernel]
  let pairs := S.powerset.product T.powerset
  let keyOf : Finset R × Finset R → Nat × Nat × Nat :=
    fun pair => pairSubsetKey pair.1 pair.2
  have hmaps : ∀ pair ∈ pairs, keyOf pair ∈ pairKeyRange S T := by
    intro pair hpair
    rcases Finset.mem_product.mp hpair with ⟨hleft, hright⟩
    have hJ := Finset.card_le_card (Finset.mem_powerset.mp hleft)
    have hK := Finset.card_le_card (Finset.mem_powerset.mp hright)
    have hI : (pair.1 ∩ pair.2).card ≤ (S ∩ T).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨Finset.mem_powerset.mp hleft hx.1,
        Finset.mem_powerset.mp hright hx.2⟩
    have hb : pair.1.card < S.card + 1 ∧
        pair.2.card < T.card + 1 ∧
          (pair.1 ∩ pair.2).card < (S ∩ T).card + 1 :=
      ⟨Nat.lt_succ_of_le hJ, Nat.lt_succ_of_le hK,
        Nat.lt_succ_of_le hI⟩
    simpa [keyOf, pairSubsetKey, pairKeyRange] using hb
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun pair => (-1 : ℝ) ^ (pair.1.card + pair.2.card) *
      u pair.1.card ^ (q - v) * u pair.2.card ^ (q' - v) *
        u (pair.1 ∪ pair.2).card ^ v)]
  apply Finset.sum_congr rfl
  intro key _hkey
  rw [pairSubsetMultiplicity]
  calc
    (∑ pair ∈ pairs with keyOf pair = key,
        (-1 : ℝ) ^ (pair.1.card + pair.2.card) *
          u pair.1.card ^ (q - v) * u pair.2.card ^ (q' - v) *
            u (pair.1 ∪ pair.2).card ^ v) =
        ∑ _pair ∈ pairs with keyOf _pair = key,
          pairCoverageTerm u q q' v key := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hkey := (Finset.mem_filter.mp hpair).2
      rw [← hkey]
      simp only [keyOf, pairSubsetKey, pairCoverageTerm]
      rw [card_union_eq_pairSubsetKey]
    _ = ((pairs.filter fun pair => keyOf pair = key).card : ℝ) *
        pairCoverageTerm u q q' v key := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Once the subset multiplicities agree, the six scalar coordinates determine
the joint coverage kernel. -/
theorem pairCoverageKernel_eq_of_multiplicities
    {R' : Type*} [DecidableEq R'] (u : Nat → ℝ)
    (S T : Finset R) (S' T' : Finset R') (q q' v : Nat)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card)
    (hmult : ∀ key, pairSubsetMultiplicity S T key =
      pairSubsetMultiplicity S' T' key) :
    pairCoverageKernel u S T q q' v =
      pairCoverageKernel u S' T' q q' v := by
  rw [pairCoverageKernel_eq_keyRangeSum,
    pairCoverageKernel_eq_keyRangeSum]
  have hrange : pairKeyRange S T = pairKeyRange S' T' := by
    simp only [pairKeyRange, hS, hT, hI]
  rw [hrange]
  apply Finset.sum_congr rfl
  intro key _hkey
  rw [hmult key]

/-- The six scalar pair coordinates determine the exact double
inclusion--exclusion coverage kernel. -/
theorem pairCoverageKernel_eq_of_coordinates
    (u : Nat → ℝ) (S T S' T' : Finset R) (q q' v : Nat)
    (hS : S.card = S'.card) (hT : T.card = T'.card)
    (hI : (S ∩ T).card = (S' ∩ T').card) :
    pairCoverageKernel u S T q q' v =
      pairCoverageKernel u S' T' q q' v := by
  apply pairCoverageKernel_eq_of_multiplicities u S T S' T' q q' v hS hT hI
  intro key
  exact pairSubsetMultiplicity_eq_of_card_inter S T S' T' hS hT hI key

end PowerLawSmallRAF

import proofs.RAF.Frankl.Antimatroid
import proofs.RAF.Frankl.Toggle

namespace RAF.Frankl

/-- A finite union-closed family with no distinguished empty row.  This is
the carrier needed by unrestricted arguments; legacy `UnionClosedData` adds
an empty-row certificate for constructions that genuinely use it. -/
structure UnionClosedCarrier (U : Type*) [DecidableEq U] where
  family : Finset (Finset U)
  union_mem : ∀ {A B}, A ∈ family → B ∈ family → A ∪ B ∈ family

/-- A finite union-closed family, explicitly including the empty member. -/
structure UnionClosedData (U : Type*) [DecidableEq U] where
  family : Finset (Finset U)
  empty_mem : ∅ ∈ family
  union_mem : ∀ {A B}, A ∈ family → B ∈ family → A ∪ B ∈ family

instance {U : Type*} [DecidableEq U] :
    Coe (UnionClosedData U) (UnionClosedCarrier U) where
  coe D := ⟨D.family, D.union_mem⟩

namespace UnionClosedData

variable {U : Type*} [DecidableEq U]

/-- The canonical interior associated with a finite union-closed family. -/
noncomputable def interior (D : UnionClosedData U) (S : Finset U) : Finset U := by
  classical
  exact (D.family.filter fun A => A ⊆ S).biUnion id

@[simp] theorem mem_interior (D : UnionClosedData U) (S : Finset U) (x : U) :
    x ∈ D.interior S ↔ ∃ A ∈ D.family, A ⊆ S ∧ x ∈ A := by
  classical
  simp [interior, and_assoc]

theorem interior_subset (D : UnionClosedData U) (S : Finset U) :
    D.interior S ⊆ S := by
  intro x hx
  rw [mem_interior] at hx
  obtain ⟨A, -, hAS, hxA⟩ := hx
  exact hAS hxA

theorem interior_mono (D : UnionClosedData U) {S T : Finset U} (hST : S ⊆ T) :
    D.interior S ⊆ D.interior T := by
  intro x hx
  rw [mem_interior] at hx ⊢
  obtain ⟨A, hAF, hAS, hxA⟩ := hx
  exact ⟨A, hAF, fun y hy => hST (hAS hy), hxA⟩

private theorem biUnion_mem (D : UnionClosedData U) :
    ∀ (G : Finset (Finset U)), G ⊆ D.family → G.biUnion id ∈ D.family := by
  classical
  intro G hG
  induction G using Finset.induction_on with
  | empty => simpa using D.empty_mem
  | @insert A G hAG ih =>
      have hAF : A ∈ D.family := hG (Finset.mem_insert_self A G)
      have hGF : G ⊆ D.family := by
        intro B hBG
        exact hG (Finset.mem_insert_of_mem hBG)
      simpa using D.union_mem hAF (ih hGF)

theorem interior_mem (D : UnionClosedData U) (S : Finset U) :
    D.interior S ∈ D.family := by
  classical
  apply D.biUnion_mem
  intro A hA
  exact (Finset.mem_filter.mp hA).1

/-- The members of a union-closed family are exactly the fixed points of its
canonical interior. -/
theorem fixed_iff_mem (D : UnionClosedData U) (S : Finset U) :
    D.interior S = S ↔ S ∈ D.family := by
  constructor
  · intro h
    rw [← h]
    exact D.interior_mem S
  · intro hSF
    apply Finset.Subset.antisymm (D.interior_subset S)
    intro x hx
    rw [mem_interior]
    exact ⟨S, hSF, Finset.Subset.rfl, hx⟩

/-- An all-blocker for coordinate `i`: deleting `B` from the universe makes
`i` absent from the canonical interior. -/
def IsBlocker [Fintype U] (D : UnionClosedData U) (i : U) (B : Finset U) : Prop :=
  i ∉ B ∧ i ∉ D.interior (Finset.univ \ B)

/-- For a selected coordinate, canonical-interior membership is exactly the
condition that every all-blocker is hit. -/
theorem mem_interior_iff_hits_blockers [Fintype U] (D : UnionClosedData U)
    {i : U} {S : Finset U} (hiS : i ∈ S) :
    i ∈ D.interior S ↔
      ∀ B : Finset U, D.IsBlocker i B → ¬ Disjoint S B := by
  constructor
  · intro hi B hB hdisj
    have hsub : S ⊆ Finset.univ \ B := by
      intro x hxS
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hxB
      exact (Finset.disjoint_left.mp hdisj) hxS hxB
    exact hB.2 (D.interior_mono hsub hi)
  · intro hhit
    by_contra hi
    let B : Finset U := Finset.univ \ S
    have hB : D.IsBlocker i B := by
      constructor
      · simp [B, hiS]
      · simpa [B] using hi
    apply hhit B hB
    rw [Finset.disjoint_left]
    intro x hxS hxB
    exact (Finset.mem_sdiff.mp hxB).2 hxS

end UnionClosedData

/-- The two reactions used to encode one coordinate. -/
inductive PairReaction (U : Type*)
  | producer : U → PairReaction U
  | gate : U → PairReaction U
  deriving DecidableEq, Fintype

/-- Molecules used by the paired universality gadget.  Markers are available
for every finite set; the CRS uses only those satisfying the blocker
predicate. -/
inductive PairMolecule (U : Type*)
  | food : PairMolecule U
  | alpha : U → PairMolecule U
  | beta : U → PairMolecule U
  | marker : U → Finset U → PairMolecule U
  deriving DecidableEq, Fintype

namespace PairGadget

universe u

variable {U : Type*} [Fintype U] [DecidableEq U]

open PairReaction PairMolecule

/-- Concrete two-reaction CRS encoding `D`. -/
noncomputable def crs (D : UnionClosedData U) :
    CRS (PairMolecule U) (PairReaction U) := by
  classical
  exact
    { inputs := fun r =>
        match r with
        | producer _ => {food}
        | gate i => insert food <|
            Finset.univ.filter fun m =>
              match m with
              | marker j B => j = i ∧ D.IsBlocker i B
              | _ => False
      outputs := fun r =>
        match r with
        | producer j => insert (alpha j) <|
            Finset.univ.filter fun m =>
              match m with
              | marker i B => D.IsBlocker i B ∧ j ∈ B
              | _ => False
        | gate i => {beta i}
      food := {food} }

/-- Each reaction is catalyzed only by its private partner product. -/
def catalysis : Catalysis (PairMolecule U) (PairReaction U)
  | beta i, producer j => i = j
  | alpha i, gate j => i = j
  | _, _ => False

/-- The paired reaction set corresponding to a coordinate set. -/
noncomputable def encode (A : Finset U) : Finset (PairReaction U) := by
  classical
  exact A.biUnion fun i => {producer i, gate i}

omit [Fintype U] in
@[simp] theorem producer_mem_encode (A : Finset U) (i : U) :
    producer i ∈ encode A ↔ i ∈ A := by
  classical
  simp [encode]

omit [Fintype U] in
@[simp] theorem gate_mem_encode (A : Finset U) (i : U) :
    gate i ∈ encode A ↔ i ∈ A := by
  classical
  simp [encode]

/-- Recover the selected coordinates from the producer reactions. -/
noncomputable def decode (S : Finset (PairReaction U)) : Finset U := by
  classical
  exact Finset.univ.filter fun i => producer i ∈ S

@[simp] theorem mem_decode (S : Finset (PairReaction U)) (i : U) :
    i ∈ decode S ↔ producer i ∈ S := by
  classical
  simp [decode]

theorem beta_origin (D : UnionClosedData U) (S : Finset (PairReaction U))
    {i : U} {k : Nat} (h : beta i ∈ closureAt (crs D) S k) :
    gate i ∈ S := by
  classical
  rcases mem_closureAt_imp_food_or_output (crs D) S h with hfood | ⟨r, hrS, hout⟩
  · simp [crs] at hfood
  · cases r with
    | producer j => simp [crs] at hout
    | gate j =>
        simp [crs] at hout
        simpa [hout] using hrS

theorem alpha_origin (D : UnionClosedData U) (S : Finset (PairReaction U))
    {i : U} {k : Nat} (h : alpha i ∈ closureAt (crs D) S k) :
    producer i ∈ S := by
  classical
  rcases mem_closureAt_imp_food_or_output (crs D) S h with hfood | ⟨r, hrS, hout⟩
  · simp [crs] at hfood
  · cases r with
    | producer j =>
        simp [crs] at hout
        simpa [hout] using hrS
    | gate j => simp [crs] at hout

theorem marker_origin (D : UnionClosedData U) (S : Finset (PairReaction U))
    {i : U} {B : Finset U} {k : Nat}
    (h : marker i B ∈ closureAt (crs D) S k) :
    D.IsBlocker i B ∧ ∃ j ∈ B, producer j ∈ S := by
  classical
  rcases mem_closureAt_imp_food_or_output (crs D) S h with hfood | ⟨r, hrS, hout⟩
  · simp [crs] at hfood
  · cases r with
    | producer j =>
        simp [crs] at hout
        exact ⟨hout.1, j, hout.2, hrS⟩
    | gate j => simp [crs] at hout

/-- Every RAF in the constructed CRS contains the two reactions of a
coordinate together. -/
theorem isRAF_paired (D : UnionClosedData U)
    {S : Finset (PairReaction U)} (hS : IsRAF (crs D) catalysis S) (i : U) :
    producer i ∈ S ↔ gate i ∈ S := by
  constructor
  · intro hi
    obtain ⟨x, k, hx, hcat⟩ := hS.2.2 (producer i) hi
    cases x with
    | food => simp [catalysis] at hcat
    | alpha j => simp [catalysis] at hcat
    | beta j =>
        simp [catalysis] at hcat
        subst j
        exact beta_origin D S hx
    | marker j B => simp [catalysis] at hcat
  · intro hi
    obtain ⟨x, k, hx, hcat⟩ := hS.2.2 (gate i) hi
    cases x with
    | food => simp [catalysis] at hcat
    | alpha j =>
        simp [catalysis] at hcat
        subst j
        exact alpha_origin D S hx
    | beta j => simp [catalysis] at hcat
    | marker j B => simp [catalysis] at hcat

theorem encode_decode_of_isRAF (D : UnionClosedData U)
    {S : Finset (PairReaction U)} (hS : IsRAF (crs D) catalysis S) :
    encode (decode S) = S := by
  classical
  ext r
  cases r with
  | producer i => simp
  | gate i =>
      rw [gate_mem_encode, mem_decode]
      exact isRAF_paired D hS i

theorem food_mem_closureAt_zero (D : UnionClosedData U)
    (A : Finset U) :
    food ∈ closureAt (crs D) (encode A) 0 := by
  simp [closureAt, crs]

theorem alpha_mem_closureAt_one (D : UnionClosedData U)
    {A : Finset U} {i : U} (hiA : i ∈ A) :
    alpha i ∈ closureAt (crs D) (encode A) 1 := by
  classical
  simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨producer i, (producer_mem_encode A i).2 hiA, ?_⟩
  have henabled : Enabled (crs D) {(food : PairMolecule U)} (producer i) := by
    simp [Enabled, crs]
  change alpha i ∈
    if Enabled (crs D) {food} (producer i) then (crs D).outputs (producer i) else ∅
  rw [if_pos henabled]
  simp [crs]

theorem marker_mem_closureAt_one (D : UnionClosedData U)
    {A B : Finset U} {i j : U}
    (hjA : j ∈ A) (hjB : j ∈ B) (hB : D.IsBlocker i B) :
    marker i B ∈ closureAt (crs D) (encode A) 1 := by
  classical
  simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨producer j, (producer_mem_encode A j).2 hjA, ?_⟩
  have henabled : Enabled (crs D) {(food : PairMolecule U)} (producer j) := by
    simp [Enabled, crs]
  change marker i B ∈
    if Enabled (crs D) {food} (producer j) then (crs D).outputs (producer j) else ∅
  rw [if_pos henabled]
  simp [crs, hB, hjB]

theorem gate_inputs_subset_closureAt_one (D : UnionClosedData U)
    {A : Finset U} (hfix : D.interior A = A) {i : U} (hiA : i ∈ A) :
    (crs D).inputs (gate i) ⊆ closureAt (crs D) (encode A) 1 := by
  classical
  intro x hx
  cases x with
  | food => simp [closureAt, closureStep, crs]
  | alpha j => simp [crs] at hx
  | beta j => simp [crs] at hx
  | marker j B =>
      simp [crs] at hx
      have hji : j = i := hx.1
      subst j
      obtain ⟨r, hrA, hrB⟩ := Finset.not_disjoint_iff.mp <|
        (D.mem_interior_iff_hits_blockers hiA).mp (by simpa [hfix] using hiA) B hx.2
      exact marker_mem_closureAt_one D hrA hrB hx.2

theorem beta_mem_closureAt_two (D : UnionClosedData U)
    {A : Finset U} (hfix : D.interior A = A) {i : U} (hiA : i ∈ A) :
    beta i ∈ closureAt (crs D) (encode A) 2 := by
  classical
  simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
  right
  refine ⟨gate i, (gate_mem_encode A i).2 hiA, ?_⟩
  have henabled : Enabled (crs D) (closureAt (crs D) (encode A) 1) (gate i) :=
    gate_inputs_subset_closureAt_one D hfix hiA
  change beta i ∈
    if Enabled (crs D) (closureAt (crs D) (encode A) 1) (gate i) then
      (crs D).outputs (gate i) else ∅
  rw [if_pos henabled]
  simp [crs]

theorem encode_isRAF_of_fixed (D : UnionClosedData U)
    {A : Finset U} (hne : A.Nonempty) (hfix : D.interior A = A) :
    IsRAF (crs D) catalysis (encode A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨i, hiA⟩ := hne
    exact ⟨producer i, (producer_mem_encode A i).2 hiA⟩
  · intro r hr
    cases r with
    | producer i =>
        exact ⟨0, by simp [crs, closureAt]⟩
    | gate i =>
        have hiA : i ∈ A := (gate_mem_encode A i).1 hr
        exact ⟨1, gate_inputs_subset_closureAt_one D hfix hiA⟩
  · intro r hr
    cases r with
    | producer i =>
        have hiA : i ∈ A := (producer_mem_encode A i).1 hr
        exact ⟨beta i, 2, beta_mem_closureAt_two D hfix hiA, by simp [catalysis]⟩
    | gate i =>
        have hiA : i ∈ A := (gate_mem_encode A i).1 hr
        exact ⟨alpha i, 1, alpha_mem_closureAt_one D hiA, by simp [catalysis]⟩

theorem fixed_of_isRAF_encode (D : UnionClosedData U)
    {A : Finset U} (hRAF : IsRAF (crs D) catalysis (encode A)) :
    D.interior A = A := by
  apply Finset.Subset.antisymm (D.interior_subset A)
  intro i hiA
  apply (D.mem_interior_iff_hits_blockers hiA).2
  intro B hB
  have hgate : gate i ∈ encode A := (gate_mem_encode A i).2 hiA
  obtain ⟨k, hk⟩ := hRAF.2.1 (gate i) hgate
  have hmarkerInput : marker i B ∈ (crs D).inputs (gate i) := by
    classical
    simp [crs, hB]
  obtain ⟨-, j, hjB, hjS⟩ := marker_origin D (encode A) (hk hmarkerInput)
  exact Finset.not_disjoint_iff.2 ⟨j, (producer_mem_encode A j).1 hjS, hjB⟩

/-- Exact correctness of the paired encoding: its nonempty RAFs are precisely
the nonempty members of the original union-closed family. -/
theorem encoded_isRAF_iff_mem (D : UnionClosedData U) (A : Finset U) :
    IsRAF (crs D) catalysis (encode A) ↔ A.Nonempty ∧ A ∈ D.family := by
  constructor
  · intro hRAF
    have henc : (encode A).Nonempty := hRAF.1
    have hne : A.Nonempty := by
      obtain ⟨r, hr⟩ := henc
      cases r with
      | producer i => exact ⟨i, (producer_mem_encode A i).1 hr⟩
      | gate i => exact ⟨i, (gate_mem_encode A i).1 hr⟩
    exact ⟨hne, (D.fixed_iff_mem A).1 (fixed_of_isRAF_encode D hRAF)⟩
  · rintro ⟨hne, hmem⟩
    exact encode_isRAF_of_fixed D hne ((D.fixed_iff_mem A).2 hmem)

omit [Fintype U] in
theorem encode_injective : Function.Injective (encode : Finset U → Finset (PairReaction U)) := by
  intro A B hAB
  ext i
  have hi := congrArg (fun S : Finset (PairReaction U) => producer i ∈ S) hAB
  simpa using hi

/-- The entire RAF family of the gadget is the injective image of the
nonempty part of the supplied union-closed family. -/
theorem rafFamily_eq_image (D : UnionClosedData U) :
    rafFamily (crs D) catalysis = (D.family.erase ∅).image encode := by
  classical
  ext S
  rw [mem_rafFamily]
  constructor
  · intro hRAF
    have hEq : encode (decode S) = S := encode_decode_of_isRAF D hRAF
    have hEncoded : IsRAF (crs D) catalysis (encode (decode S)) := by
      rw [hEq]
      exact hRAF
    have hData := (encoded_isRAF_iff_mem D (decode S)).1 hEncoded
    rw [Finset.mem_image]
    exact ⟨decode S, Finset.mem_erase.mpr ⟨hData.1.ne_empty, hData.2⟩, hEq⟩
  · rw [Finset.mem_image]
    rintro ⟨A, hA, rfl⟩
    have hParts := Finset.mem_erase.mp hA
    exact (encoded_isRAF_iff_mem D A).2
      ⟨Finset.nonempty_iff_ne_empty.mpr hParts.1, hParts.2⟩

theorem rafFamily_card (D : UnionClosedData U) :
    (rafFamily (crs D) catalysis).card = (D.family.erase ∅).card := by
  classical
  rw [rafFamily_eq_image, Finset.card_image_of_injective _ encode_injective]

/-- Adjoining the unique empty member recovers the original family size. -/
theorem rafFamily_card_add_one (D : UnionClosedData U) :
    (rafFamily (crs D) catalysis).card + 1 = D.family.card := by
  classical
  rw [rafFamily_card, Finset.card_erase_add_one D.empty_mem]

/-- A producer occurs in exactly the encoded family members containing its
coordinate. -/
theorem producer_frequency (D : UnionClosedData U) (i : U) :
    frequency (crs D) catalysis (producer i) =
      (D.family.filter fun A => i ∈ A).card := by
  classical
  letI : DecidableEq (PairReaction U) := Classical.decEq _
  unfold frequency
  apply Finset.card_bij (fun S _ => decode S)
  · intro S hS
    have hParts := Finset.mem_filter.mp hS
    have hRAF := (mem_rafFamily (crs D) catalysis S).1 hParts.1
    have hEq := encode_decode_of_isRAF D hRAF
    have hEncoded : IsRAF (crs D) catalysis (encode (decode S)) := by
      rw [hEq]
      exact hRAF
    have hData := (encoded_isRAF_iff_mem D (decode S)).1 hEncoded
    exact Finset.mem_filter.mpr ⟨hData.2, (mem_decode S i).2 hParts.2⟩
  · intro S hS T hT hDecode
    have hSRAF := (mem_rafFamily (crs D) catalysis S).1 (Finset.mem_filter.mp hS).1
    have hTRAF := (mem_rafFamily (crs D) catalysis T).1 (Finset.mem_filter.mp hT).1
    calc
      S = encode (decode S) := (encode_decode_of_isRAF D hSRAF).symm
      _ = encode (decode T) := congrArg encode hDecode
      _ = T := encode_decode_of_isRAF D hTRAF
  · intro A hA
    have hParts := Finset.mem_filter.mp hA
    have hne : A.Nonempty := ⟨i, hParts.2⟩
    have hRAF := (encoded_isRAF_iff_mem D A).2 ⟨hne, hParts.1⟩
    refine ⟨encode A, Finset.mem_filter.mpr
      ⟨(mem_rafFamily (crs D) catalysis (encode A)).2 hRAF,
        (producer_mem_encode A i).2 hParts.2⟩, ?_⟩
    ext j
    simp [decode]

/-- The gate paired with a coordinate has the same exact frequency. -/
theorem gate_frequency (D : UnionClosedData U) (i : U) :
    frequency (crs D) catalysis (gate i) =
      (D.family.filter fun A => i ∈ A).card := by
  classical
  letI : DecidableEq (PairReaction U) := Classical.decEq _
  unfold frequency
  apply Finset.card_bij (fun S _ => decode S)
  · intro S hS
    have hParts := Finset.mem_filter.mp hS
    have hRAF := (mem_rafFamily (crs D) catalysis S).1 hParts.1
    have hEq := encode_decode_of_isRAF D hRAF
    have hEncoded : IsRAF (crs D) catalysis (encode (decode S)) := by
      rw [hEq]
      exact hRAF
    have hData := (encoded_isRAF_iff_mem D (decode S)).1 hEncoded
    have hproducer : producer i ∈ S := (isRAF_paired D hRAF i).2 hParts.2
    exact Finset.mem_filter.mpr ⟨hData.2, (mem_decode S i).2 hproducer⟩
  · intro S hS T hT hDecode
    have hSRAF := (mem_rafFamily (crs D) catalysis S).1 (Finset.mem_filter.mp hS).1
    have hTRAF := (mem_rafFamily (crs D) catalysis T).1 (Finset.mem_filter.mp hT).1
    calc
      S = encode (decode S) := (encode_decode_of_isRAF D hSRAF).symm
      _ = encode (decode T) := congrArg encode hDecode
      _ = T := encode_decode_of_isRAF D hTRAF
  · intro A hA
    have hParts := Finset.mem_filter.mp hA
    have hne : A.Nonempty := ⟨i, hParts.2⟩
    have hRAF := (encoded_isRAF_iff_mem D A).2 ⟨hne, hParts.1⟩
    refine ⟨encode A, Finset.mem_filter.mpr
      ⟨(mem_rafFamily (crs D) catalysis (encode A)).2 hRAF,
        (gate_mem_encode A i).2 hParts.2⟩, ?_⟩
    ext j
    simp [decode]

/-- Frankl's inequality for a concrete finite union-closed family containing
the empty set. The premise merely says that a nonempty member exists. -/
def UnionClosedFrankl (D : UnionClosedData U) : Prop :=
  (D.family.erase ∅).Nonempty →
    ∃ i : U, D.family.card ≤ 2 * (D.family.filter fun A => i ∈ A).card

/-- The strong RAF half-frequency statement for the pair gadget implies
Frankl's conjecture for the arbitrary family from which it was built. -/
theorem rafFixedFrankl_implies_unionClosedFrankl (D : UnionClosedData U)
    (hRAFFrankl : RAFFixedFrankl (crs D) catalysis) :
    UnionClosedFrankl D := by
  intro hFamily
  have hRAFs : (rafFamily (crs D) catalysis).Nonempty := by
    obtain ⟨A, hAerase⟩ := hFamily
    have hA := Finset.mem_erase.mp hAerase
    have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA.1
    exact ⟨encode A, (mem_rafFamily (crs D) catalysis (encode A)).2
      ((encoded_isRAF_iff_mem D A).2 ⟨hne, hA.2⟩)⟩
  obtain ⟨r, hr⟩ := hRAFFrankl hRAFs
  cases r with
  | producer i =>
      refine ⟨i, ?_⟩
      rw [rafFamily_card_add_one D, producer_frequency D i] at hr
      exact hr
  | gate i =>
      refine ⟨i, ?_⟩
      rw [rafFamily_card_add_one D, gate_frequency D i] at hr
      exact hr

/-- A universal positive answer to the RAF fixed-family question would solve
the classical union-closed sets conjecture. -/
theorem all_rafFixedFrankl_implies_all_unionClosedFrankl
    (hAll : ∀ (M R : Type u) [Fintype R] [DecidableEq M] [DecidableEq R],
      ∀ (Q : CRS M R) (C : Catalysis M R), RAFFixedFrankl Q C) :
    ∀ (U : Type u) [Fintype U] [DecidableEq U],
      ∀ D : UnionClosedData U, UnionClosedFrankl D := by
  intro U _ _ D
  exact rafFixedFrankl_implies_unionClosedFrankl D
    (hAll (PairMolecule U) (PairReaction U) (crs D) catalysis)

/-- The fixed family of any finite CRS, packaged as union-closed data. -/
noncomputable def fixedData {M R : Type*} [Fintype R]
    [DecidableEq M] [DecidableEq R] (Q : CRS M R) (C : Catalysis M R) :
    UnionClosedData R where
  family := fixedFamily Q C
  empty_mem := by simp
  union_mem := by
    intro A B hA hB
    exact fixedFamily_union_closed Q C hA hB

theorem fixedData_card {M R : Type*} [Fintype R]
    [DecidableEq M] [DecidableEq R] (Q : CRS M R) (C : Catalysis M R) :
    (fixedData Q C).family.card = (rafFamily Q C).card + 1 := by
  classical
  have hempty : (∅ : Finset R) ∉ rafFamily Q C := by
    intro h
    have hRAF := (mem_rafFamily Q C ∅).1 h
    exact hRAF.1.ne_empty rfl
  change (fixedFamily Q C).card = (rafFamily Q C).card + 1
  simp [fixedFamily, hempty]

theorem fixedData_frequency {M R : Type*} [Fintype R]
    [DecidableEq M] [DecidableEq R] (Q : CRS M R) (C : Catalysis M R) (r : R) :
    ((fixedData Q C).family.filter fun S => r ∈ S).card = frequency Q C r := by
  classical
  rw [frequency_eq_filter_card]
  change ((fixedFamily Q C).filter fun S => r ∈ S).card = _
  congr 1
  ext S
  simp only [Finset.mem_filter, mem_fixedFamily, mem_rafFamily]
  constructor
  · rintro ⟨hFixed, hrS⟩
    rcases hFixed with rfl | hRAF
    · simp at hrS
    · exact ⟨hRAF, hrS⟩
  · rintro ⟨hRAF, hrS⟩
    exact ⟨Or.inr hRAF, hrS⟩

/-- Conversely, Frankl's conjecture for all finite union-closed families
implies the strong RAF fixed-family statement for every finite CRS. -/
theorem all_unionClosedFrankl_implies_all_rafFixedFrankl
    (hAll : ∀ (U : Type u) [Fintype U] [DecidableEq U],
      ∀ D : UnionClosedData U, UnionClosedFrankl D) :
    ∀ (M R : Type u) [Fintype R] [DecidableEq M] [DecidableEq R],
      ∀ (Q : CRS M R) (C : Catalysis M R), RAFFixedFrankl Q C := by
  intro M R _ _ _ Q C hRAFs
  let D : UnionClosedData R := fixedData Q C
  have hFamily : (D.family.erase ∅).Nonempty := by
    obtain ⟨S, hS⟩ := hRAFs
    have hRAF := (mem_rafFamily Q C S).1 hS
    have hFixed : S ∈ D.family := by
      change S ∈ fixedFamily Q C
      rw [mem_fixedFamily]
      exact Or.inr hRAF
    exact ⟨S, Finset.mem_erase.mpr ⟨hRAF.1.ne_empty, hFixed⟩⟩
  obtain ⟨r, hr⟩ := hAll R D hFamily
  refine ⟨r, ?_⟩
  change (rafFamily Q C).card + 1 ≤ 2 * frequency Q C r
  rw [← fixedData_card Q C, ← fixedData_frequency Q C r]
  exact hr

/-- The universal RAF fixed-family conjecture is logically equivalent to the
classical union-closed sets conjecture (at each universe level). -/
theorem all_rafFixedFrankl_iff_all_unionClosedFrankl :
    (∀ (M R : Type u) [Fintype R] [DecidableEq M] [DecidableEq R],
      ∀ (Q : CRS M R) (C : Catalysis M R), RAFFixedFrankl Q C) ↔
    (∀ (U : Type u) [Fintype U] [DecidableEq U],
      ∀ D : UnionClosedData U, UnionClosedFrankl D) := by
  exact ⟨all_rafFixedFrankl_implies_all_unionClosedFrankl,
    all_unionClosedFrankl_implies_all_rafFixedFrankl⟩

end PairGadget

end RAF.Frankl

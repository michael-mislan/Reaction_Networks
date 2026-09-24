import proofs.IrrRAFEnumeration.FullCover

namespace IrrRAFEnumeration

/-- A block has two switch vertices and three vertices common to both choices. -/
abbrev ProductVertex (b : Nat) := Fin b × (Bool ⊕ Fin 3)

/-- A fixed finite order used only to make the ordered-cover construction
canonical.  None of the cardinal or blocker statements depends on which
finite enumeration supplies this order. -/
noncomputable instance productVertexLinearOrder (b : Nat) :
    LinearOrder (ProductVertex b) := by
  let vertexEquiv := Fintype.equivFin (ProductVertex b)
  exact LinearOrder.lift' vertexEquiv vertexEquiv.injective

/-- One positive edge chooses one switch vertex in every block and contains all
three universal vertices in every block. -/
noncomputable def switchProductEdge {b : Nat} (choice : Fin b → Bool) :
    Finset (ProductVertex b) := by
  classical
  exact Finset.univ.filter fun vertex =>
    match vertex.2 with
    | Sum.inl switch => switch = choice vertex.1
    | Sum.inr _ => True

noncomputable def switchProductFamily (b : Nat) :
    Finset (Finset (ProductVertex b)) :=
  Finset.univ.image switchProductEdge

@[simp] theorem mem_switchProductEdge {b : Nat} (choice : Fin b → Bool)
    (vertex : ProductVertex b) :
    vertex ∈ switchProductEdge choice ↔
      match vertex.2 with
      | Sum.inl switch => switch = choice vertex.1
      | Sum.inr _ => True := by
  simp [switchProductEdge]

theorem switchProductEdge_injective {b : Nat} :
    Function.Injective (switchProductEdge : (Fin b → Bool) →
      Finset (ProductVertex b)) := by
  intro choice other hEdges
  funext block
  have hmem := Finset.ext_iff.mp hEdges (block, Sum.inl (choice block))
  simpa using hmem

theorem switchProductFamily_card (b : Nat) :
    (switchProductFamily b).card = 2 ^ b := by
  classical
  rw [switchProductFamily,
    Finset.card_image_iff.mpr fun choice _ other _ hEdges =>
      switchProductEdge_injective hEdges]
  simp

/-- Restricting a Boolean choice at one coordinate is equivalent to choosing
freely on every other coordinate. -/
def fixedChoiceEquiv {b : Nat} (block : Fin b) (value : Bool) :
    {choice : Fin b → Bool // choice block = value} ≃
      ({other : Fin b // other ≠ block} → Bool) where
  toFun choice other := choice.1 other.1
  invFun parts :=
    ⟨fun other => if h : other = block then value else parts ⟨other, h⟩, by simp⟩
  left_inv choice := by
    apply Subtype.ext
    funext other
    by_cases h : other = block
    · subst other
      simp [choice.2]
    · simp [h]
  right_inv parts := by
    funext other
    simp [other.2]

theorem fixedChoice_card {b : Nat} (block : Fin b) (value : Bool) :
    (Finset.univ.filter fun choice : Fin b → Bool =>
      choice block = value).card = 2 ^ (b - 1) := by
  classical
  calc
    (Finset.univ.filter fun choice : Fin b → Bool =>
        choice block = value).card =
        Fintype.card {choice : Fin b → Bool // choice block = value} := by
      simp [Fintype.card_subtype]
    _ = Fintype.card ({other : Fin b // other ≠ block} → Bool) :=
      Fintype.card_congr (fixedChoiceEquiv block value)
    _ = 2 ^ (b - 1) := by simp [Fintype.card_subtype_compl]

/-- Members of a family that contain one specified vertex. -/
def familyVertexFiber {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (vertex : α) : Finset (Finset α) :=
  F.filter fun E => vertex ∈ E

theorem switchProduct_switchFiber_eq {b : Nat} (block : Fin b)
    (value : Bool) :
    familyVertexFiber (switchProductFamily b) (block, Sum.inl value) =
      (Finset.univ.filter fun choice : Fin b → Bool =>
        choice block = value).image switchProductEdge := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨hFamily, hvertex⟩ := Finset.mem_filter.mp hE
    obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hFamily
    apply Finset.mem_image.mpr
    refine ⟨choice, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hvalue : value = choice block := by simpa using hvertex
    exact hvalue.symm
  · intro hE
    obtain ⟨choice, hchoice, rfl⟩ := Finset.mem_image.mp hE
    have hfixed := (Finset.mem_filter.mp hchoice).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩, by
      simpa using hfixed.symm⟩

theorem switchProduct_switchFiber_card {b : Nat} (block : Fin b)
    (value : Bool) :
    (familyVertexFiber (switchProductFamily b)
      (block, Sum.inl value)).card = 2 ^ (b - 1) := by
  classical
  rw [switchProduct_switchFiber_eq,
    Finset.card_image_iff.mpr fun left _ right _ hEq =>
      switchProductEdge_injective hEq,
    fixedChoice_card]

theorem switchProduct_universalFiber_eq {b : Nat} (block : Fin b)
    (point : Fin 3) :
    familyVertexFiber (switchProductFamily b) (block, Sum.inr point) =
      switchProductFamily b := by
  classical
  ext E
  constructor
  · exact fun hE => (Finset.mem_filter.mp hE).1
  · intro hE
    obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hE
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩, by simp⟩

theorem switchProduct_universalFiber_card {b : Nat} (block : Fin b)
    (point : Fin 3) :
    (familyVertexFiber (switchProductFamily b)
      (block, Sum.inr point)).card = 2 ^ b := by
  rw [switchProduct_universalFiber_eq, switchProductFamily_card]

/-- The three singleton blockers associated with one block. -/
def universalBlockers (b : Nat) :
    Finset (Finset (ProductVertex b)) :=
  (Finset.univ.product (Finset.univ : Finset (Fin 3))).image fun blockPoint =>
    {(blockPoint.1, Sum.inr blockPoint.2)}

/-- The fourth blocker associated with one block contains its two switches. -/
def switchBlocker {b : Nat} (block : Fin b) :
    Finset (ProductVertex b) :=
  {(block, Sum.inl false), (block, Sum.inl true)}

def switchBlockers (b : Nat) :
    Finset (Finset (ProductVertex b)) :=
  Finset.univ.image switchBlocker

def switchProductDual (b : Nat) :
    Finset (Finset (ProductVertex b)) :=
  universalBlockers b ∪ switchBlockers b

/-- The unique component blocker containing a given component vertex. -/
def dualMemberForVertex {b : Nat} (vertex : ProductVertex b) :
    Finset (ProductVertex b) :=
  match vertex.2 with
  | Sum.inl _ => switchBlocker vertex.1
  | Sum.inr point => {(vertex.1, Sum.inr point)}

theorem mem_switchProductDual_and_vertex_iff {b : Nat}
    (vertex : ProductVertex b) (D : Finset (ProductVertex b)) :
    D ∈ switchProductDual b ∧ vertex ∈ D ↔
      D = dualMemberForVertex vertex := by
  classical
  rcases vertex with ⟨block, switch | point⟩
  · constructor
    · rintro ⟨hD, hvertex⟩
      rcases Finset.mem_union.mp hD with hUniversal | hSwitch
      · obtain ⟨blockPoint, _, rfl⟩ := Finset.mem_image.mp hUniversal
        rcases blockPoint with ⟨otherBlock, otherPoint⟩
        simp at hvertex
      · obtain ⟨otherBlock, _, rfl⟩ := Finset.mem_image.mp hSwitch
        have hblock : block = otherBlock := by
          simp [switchBlocker] at hvertex
          rcases hvertex with hfalse | htrue
          · exact hfalse.1
          · exact htrue.1
        subst otherBlock
        rfl
    · rintro rfl
      exact ⟨Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨block, Finset.mem_univ _, rfl⟩), by
          simp [dualMemberForVertex, switchBlocker]⟩
  · constructor
    · rintro ⟨hD, hvertex⟩
      rcases Finset.mem_union.mp hD with hUniversal | hSwitch
      · obtain ⟨blockPoint, _, rfl⟩ := Finset.mem_image.mp hUniversal
        rcases blockPoint with ⟨otherBlock, otherPoint⟩
        have heq : (block, Sum.inr point) =
            (otherBlock, Sum.inr otherPoint) :=
          Finset.mem_singleton.mp hvertex
        cases heq
        rfl
      · obtain ⟨otherBlock, _, rfl⟩ := Finset.mem_image.mp hSwitch
        simp [switchBlocker] at hvertex
    · rintro rfl
      exact ⟨Finset.mem_union_left _
        (Finset.mem_image.mpr
          ⟨(block, point), Finset.mem_product.mpr
            ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩), by
              simp [dualMemberForVertex]⟩

theorem switchProductDual_vertexFiber_eq {b : Nat}
    (vertex : ProductVertex b) :
    familyVertexFiber (switchProductDual b) vertex =
      {dualMemberForVertex vertex} := by
  classical
  ext D
  simp only [familyVertexFiber, Finset.mem_filter, Finset.mem_singleton]
  exact mem_switchProductDual_and_vertex_iff vertex D

theorem switchProductDual_vertexFiber_card {b : Nat}
    (vertex : ProductVertex b) :
    (familyVertexFiber (switchProductDual b) vertex).card = 1 := by
  rw [switchProductDual_vertexFiber_eq]
  simp

theorem universalBlocker_map_injective {b : Nat} :
    Function.Injective (fun blockPoint : Fin b × Fin 3 =>
      ({(blockPoint.1, Sum.inr blockPoint.2)} :
        Finset (ProductVertex b))) := by
  intro left right h
  have hsingle :
      (left.1, Sum.inr left.2) = (right.1, Sum.inr right.2) :=
    Finset.singleton_injective h
  exact Prod.ext (congrArg (fun x => x.1) hsingle)
    (Sum.inr_injective (congrArg (fun x => x.2) hsingle))

theorem switchBlocker_injective {b : Nat} :
    Function.Injective (switchBlocker : Fin b → Finset (ProductVertex b)) := by
  intro left right h
  have hmem := Finset.ext_iff.mp h (left, Sum.inl false)
  simp [switchBlocker] at hmem
  exact hmem

theorem universalBlockers_card (b : Nat) :
    (universalBlockers b).card = 3 * b := by
  classical
  rw [universalBlockers,
    Finset.card_image_iff.mpr fun left _ right _ h =>
      universalBlocker_map_injective h]
  simp [Nat.mul_comm]

theorem switchBlockers_card (b : Nat) :
    (switchBlockers b).card = b := by
  classical
  rw [switchBlockers,
    Finset.card_image_iff.mpr fun left _ right _ h =>
      switchBlocker_injective h]
  simp

theorem universalBlockers_disjoint_switchBlockers (b : Nat) :
    Disjoint (universalBlockers b) (switchBlockers b) := by
  classical
  rw [Finset.disjoint_left]
  intro edge hUniversal hSwitch
  obtain ⟨blockPoint, _, rfl⟩ := Finset.mem_image.mp hUniversal
  obtain ⟨block, _, hEq⟩ := Finset.mem_image.mp hSwitch
  have hcard := congrArg Finset.card hEq
  simp [switchBlocker] at hcard

theorem switchProductDual_card (b : Nat) :
    (switchProductDual b).card = 4 * b := by
  rw [switchProductDual,
    Finset.card_union_of_disjoint (universalBlockers_disjoint_switchBlockers b),
    universalBlockers_card, switchBlockers_card]
  omega

theorem switchProductEdge_mem_family {b : Nat} (choice : Fin b → Bool) :
    switchProductEdge choice ∈ switchProductFamily b := by
  classical
  exact Finset.mem_image.mpr ⟨choice, Finset.mem_univ _, rfl⟩

theorem universalBlocker_mem {b : Nat} (block : Fin b) (point : Fin 3) :
    ({(block, Sum.inr point)} : Finset (ProductVertex b)) ∈
      universalBlockers b := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(block, point), by simp, rfl⟩

theorem switchBlocker_mem {b : Nat} (block : Fin b) :
    switchBlocker block ∈ switchBlockers b := by
  classical
  exact Finset.mem_image.mpr ⟨block, Finset.mem_univ _, rfl⟩

/-- A set hits the product family precisely when one block contains either a
universal vertex or both switch vertices. -/
theorem hits_switchProductFamily_iff {b : Nat}
    (T : Finset (ProductVertex b)) :
    Hits (switchProductFamily b) T ↔
      (∃ block point,
        ({(block, Sum.inr point)} : Finset (ProductVertex b)) ⊆ T) ∨
      (∃ block, switchBlocker block ⊆ T) := by
  classical
  constructor
  · intro hHits
    by_contra hWitness
    push Not at hWitness
    have hNoUniversal :
        ∀ block point, (block, Sum.inr point) ∉ T := by
      intro block point hmem
      exact hWitness.1 block point (by simpa using hmem)
    have hNotBoth :
        ∀ block, ¬((block, Sum.inl false) ∈ T ∧
          (block, Sum.inl true) ∈ T) := by
      intro block hboth
      apply hWitness.2 block
      intro vertex hvertex
      simp only [switchBlocker, Finset.mem_insert,
        Finset.mem_singleton] at hvertex
      rcases hvertex with rfl | rfl
      · exact hboth.1
      · exact hboth.2
    let choice : Fin b → Bool := fun block =>
      if (block, Sum.inl false) ∈ T then true else false
    have hDisjoint : Disjoint T (switchProductEdge choice) := by
      rw [Finset.disjoint_left]
      intro vertex hvertexT hvertexEdge
      rcases vertex with ⟨block, switch | point⟩
      · simp only [mem_switchProductEdge] at hvertexEdge
        cases switch with
        | false =>
            have hfalse : (block, Sum.inl false) ∈ T := hvertexT
            simp [choice, hfalse] at hvertexEdge
        | true =>
            by_cases hfalse : (block, Sum.inl false) ∈ T
            · exact hNotBoth block ⟨hfalse, hvertexT⟩
            · simp [choice, hfalse] at hvertexEdge
      · exact hNoUniversal block point hvertexT
    exact hHits (switchProductEdge choice)
      (switchProductEdge_mem_family choice) hDisjoint
  · rintro (⟨block, point, hsubset⟩ | ⟨block, hsubset⟩)
    · intro edge hEdge
      obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hEdge
      exact Finset.not_disjoint_iff.mpr
        ⟨(block, Sum.inr point), hsubset (by simp), by simp⟩
    · intro edge hEdge
      obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hEdge
      exact Finset.not_disjoint_iff.mpr
        ⟨(block, Sum.inl (choice block)), hsubset (by
          simp [switchBlocker]), by simp⟩

theorem hits_switchProductFamily_iff_contains_dual {b : Nat}
    (T : Finset (ProductVertex b)) :
    Hits (switchProductFamily b) T ↔
      ∃ D ∈ switchProductDual b, D ⊆ T := by
  classical
  rw [hits_switchProductFamily_iff]
  constructor
  · rintro (⟨block, point, hsubset⟩ | ⟨block, hsubset⟩)
    · exact ⟨{(block, Sum.inr point)}, by
        simp [switchProductDual, universalBlocker_mem], hsubset⟩
    · exact ⟨switchBlocker block, by
        simp [switchProductDual, switchBlocker_mem], hsubset⟩
  · rintro ⟨D, hD, hsubset⟩
    simp only [switchProductDual, Finset.mem_union] at hD
    rcases hD with hUniversal | hSwitch
    · obtain ⟨⟨block, point⟩, _, rfl⟩ := Finset.mem_image.mp hUniversal
      exact Or.inl ⟨block, point, hsubset⟩
    · obtain ⟨block, _, rfl⟩ := Finset.mem_image.mp hSwitch
      exact Or.inr ⟨block, hsubset⟩

theorem switchProductDual_isClutter (b : Nat) :
    IsClutter (switchProductDual b) := by
  classical
  intro A hA B hB hAB
  simp only [switchProductDual, Finset.mem_union] at hA hB
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · obtain ⟨left, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨right, _, rfl⟩ := Finset.mem_image.mp hB
    have hpoint := hAB (show (left.1, Sum.inr left.2) ∈
      ({(left.1, Sum.inr left.2)} : Finset (ProductVertex b)) by simp)
    simp only [Finset.mem_singleton] at hpoint
    simp [← hpoint]
  · obtain ⟨left, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨right, _, rfl⟩ := Finset.mem_image.mp hB
    have hpoint := hAB (show (left.1, Sum.inr left.2) ∈
      ({(left.1, Sum.inr left.2)} : Finset (ProductVertex b)) by simp)
    simp [switchBlocker] at hpoint
  · obtain ⟨left, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨right, _, rfl⟩ := Finset.mem_image.mp hB
    have hfalse := hAB (show (left, Sum.inl false) ∈ switchBlocker left by
      simp [switchBlocker])
    simp at hfalse
  · obtain ⟨left, _, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨right, _, rfl⟩ := Finset.mem_image.mp hB
    have hfalse := hAB (show (left, Sum.inl false) ∈ switchBlocker left by
      simp [switchBlocker])
    simp [switchBlocker] at hfalse
    subst right
    exact Finset.Subset.rfl

/-- The displayed `4b`-member family is exactly the blocker of the
`2^b`-member product clutter. -/
theorem switchProduct_blocker_eq (b : Nat) :
    blocker (switchProductFamily b) = switchProductDual b := by
  classical
  ext T
  rw [mem_blocker]
  constructor
  · intro hMinimal
    obtain ⟨D, hDdual, hDT⟩ :=
      (hits_switchProductFamily_iff_contains_dual T).mp hMinimal.1
    have hDHits : Hits (switchProductFamily b) D :=
      (hits_switchProductFamily_iff_contains_dual D).mpr
        ⟨D, hDdual, Finset.Subset.rfl⟩
    have hTD : T ⊆ D := hMinimal.2 hDHits hDT
    simpa [Finset.Subset.antisymm hDT hTD] using hDdual
  · intro hTdual
    refine ⟨(hits_switchProductFamily_iff_contains_dual T).mpr
      ⟨T, hTdual, Finset.Subset.rfl⟩, ?_⟩
    intro K hKHits hKT
    obtain ⟨D, hDdual, hDK⟩ :=
      (hits_switchProductFamily_iff_contains_dual K).mp hKHits
    exact (switchProductDual_isClutter b D hDdual T hTdual
      (hDK.trans hKT)).trans hDK

theorem switchProduct_blocker_card (b : Nat) :
    (blocker (switchProductFamily b)).card = 4 * b := by
  rw [switchProduct_blocker_eq, switchProductDual_card]

/-- The lexicographically first product edge, used by the hybrid strong-cover
branch. -/
noncomputable def selectedProductEdge (b : Nat) : Finset (ProductVertex b) :=
  switchProductEdge fun _ => false

noncomputable def productCoverRegion {b : Nat} (block : Fin b)
    (choice : Fin b → Bool) :
    Finset (ProductVertex b) :=
  let point : ProductVertex b := (block, Sum.inr 0)
  insert point ((Finset.univ \ prior (selectedProductEdge b) point) \
    switchProductEdge choice)

theorem selectedProductEdge_mem_family (b : Nat) :
    selectedProductEdge b ∈ switchProductFamily b := by
  exact switchProductEdge_mem_family fun _ => false

theorem productCoverRegion_mem_strongCover {b : Nat}
    (block : Fin b) (choice : Fin b → Bool) :
    productCoverRegion block choice ∈
      strongMemberFullCover (switchProductFamily b) (selectedProductEdge b) := by
  classical
  simp only [strongMemberFullCover, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨switchProductEdge choice, switchProductEdge_mem_family choice,
    (block, Sum.inr 0), ?_, rfl⟩
  simp [selectedProductEdge]

@[simp] theorem universal_mem_productCoverRegion_iff {b : Nat}
    (block index : Fin b) (point : Fin 3) (choice : Fin b → Bool) :
    (index, Sum.inr point) ∈ productCoverRegion block choice ↔
      index = block ∧ point = 0 := by
  classical
  simp [productCoverRegion]

@[simp] theorem trueSwitch_mem_productCoverRegion_iff {b : Nat}
    (block index : Fin b) (choice : Fin b → Bool) :
    (index, Sum.inl true) ∈ productCoverRegion block choice ↔
      choice index = false := by
  classical
  simp [productCoverRegion, prior, selectedProductEdge]

theorem productCoverRegion_injective {b : Nat} :
    Function.Injective (fun code : Fin b × (Fin b → Bool) =>
      productCoverRegion code.1 code.2) := by
  classical
  rintro ⟨block, choice⟩ ⟨otherBlock, otherChoice⟩ hRegions
  have hBlockMem := Finset.ext_iff.mp hRegions (block, Sum.inr 0)
  have hBlock : block = otherBlock := by
    simpa using hBlockMem
  subst otherBlock
  have hChoice : choice = otherChoice := by
    funext index
    have hSwitch := Finset.ext_iff.mp hRegions (index, Sum.inl true)
    simp only [trueSwitch_mem_productCoverRegion_iff] at hSwitch
    cases hLeft : choice index <;> cases hRight : otherChoice index <;>
      simp [hLeft, hRight] at hSwitch ⊢
  exact Prod.ext rfl hChoice

/-- A concrete exponential lower bound on the ordered strong cover.  One
universal distinguished point per block already yields a different region for
every Boolean product edge. -/
theorem strongProductCover_card_ge (b : Nat) :
    b * 2 ^ b ≤
      (strongMemberFullCover (switchProductFamily b)
        (selectedProductEdge b)).card := by
  classical
  let codes : Finset (Fin b × (Fin b → Bool)) := Finset.univ
  let regions := codes.image fun code =>
    productCoverRegion code.1 code.2
  have hRegions : regions ⊆
      strongMemberFullCover (switchProductFamily b)
        (selectedProductEdge b) := by
    intro region hRegion
    obtain ⟨code, _, rfl⟩ := Finset.mem_image.mp hRegion
    exact productCoverRegion_mem_strongCover code.1 code.2
  calc
    b * 2 ^ b = codes.card := by simp [codes]
    _ = regions.card := by
      exact (Finset.card_image_iff.mpr fun left _ right _ h =>
        productCoverRegion_injective h).symm
    _ ≤ _ := Finset.card_le_card hRegions

end IrrRAFEnumeration

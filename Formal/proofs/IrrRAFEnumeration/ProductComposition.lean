import proofs.IrrRAFEnumeration.ProductClutter

namespace IrrRAFEnumeration

/-- Vertices of `r` disjoint copies of the product component. -/
abbrev StagedProductVertex (r b : Nat) := Fin r × ProductVertex b

noncomputable instance stagedProductVertexLinearOrder (r b : Nat) :
    LinearOrder (StagedProductVertex r b) := by
  let vertexEquiv := Fintype.equivFin (StagedProductVertex r b)
  exact LinearOrder.lift' vertexEquiv vertexEquiv.injective

/-- Embed a component set into one disjoint stage. -/
def stageLift {r b : Nat} (stage : Fin r) (A : Finset (ProductVertex b)) :
    Finset (StagedProductVertex r b) :=
  A.image fun x => (stage, x)

/-- Restrict a staged set to one component and remove its stage tag. -/
def stageSection {r b : Nat} (D : Finset (StagedProductVertex r b))
    (stage : Fin r) : Finset (ProductVertex b) :=
  (D.filter fun x => x.1 = stage).image fun x => x.2

@[simp] theorem mem_stageLift {r b : Nat} (stage : Fin r)
    (A : Finset (ProductVertex b)) (other : Fin r) (x : ProductVertex b) :
    (other, x) ∈ stageLift stage A ↔ other = stage ∧ x ∈ A := by
  classical
  constructor
  · intro h
    obtain ⟨y, hyA, hyEq⟩ := Finset.mem_image.mp h
    have hstage : stage = other := congrArg Prod.fst hyEq
    have hyx : y = x := congrArg Prod.snd hyEq
    exact ⟨hstage.symm, hyx ▸ hyA⟩
  · rintro ⟨rfl, hxA⟩
    exact Finset.mem_image.mpr ⟨x, hxA, rfl⟩

@[simp] theorem mem_stageSection {r b : Nat}
    (D : Finset (StagedProductVertex r b)) (stage : Fin r)
    (x : ProductVertex b) :
    x ∈ stageSection D stage ↔ (stage, x) ∈ D := by
  classical
  simp [stageSection]

/-- The disjoint union of the component input families. -/
noncomputable def stagedProductFamily (r b : Nat) :
    Finset (Finset (StagedProductVertex r b)) :=
  Finset.univ.biUnion fun stage =>
    (switchProductFamily b).image (stageLift stage)

@[simp] theorem mem_stagedProductFamily {r b : Nat}
    (A : Finset (StagedProductVertex r b)) :
    A ∈ stagedProductFamily r b ↔
      ∃ stage : Fin r, ∃ E ∈ switchProductFamily b,
        stageLift stage E = A := by
  classical
  simp [stagedProductFamily]

/-- Hitting the disjoint union is exactly componentwise hitting.  This is the
logical factorization used by the outer product construction. -/
theorem hits_stagedProductFamily_iff {r b : Nat}
    (D : Finset (StagedProductVertex r b)) :
    Hits (stagedProductFamily r b) D ↔
      ∀ stage : Fin r, Hits (switchProductFamily b) (stageSection D stage) := by
  classical
  constructor
  · intro hHits stage E hEF hDisjoint
    apply hHits (stageLift stage E)
    · exact (mem_stagedProductFamily (A := stageLift stage E)).mpr
        ⟨stage, E, hEF, rfl⟩
    · rw [Finset.disjoint_left]
      rintro ⟨other, x⟩ hvertexD hvertexLift
      obtain ⟨hstage, hvertexE⟩ :=
        (mem_stageLift stage E other x).mp hvertexLift
      have hsection : x ∈ stageSection D stage := by
        subst other
        simpa using hvertexD
      exact (Finset.disjoint_left.mp hDisjoint) hsection hvertexE
  · intro hSections A hAF hDisjoint
    obtain ⟨stage, E, hEF, rfl⟩ :=
      (mem_stagedProductFamily (A := A)).mp hAF
    apply (hSections stage) E hEF
    rw [Finset.disjoint_left]
    intro x hxSection hxE
    have hxD : (stage, x) ∈ D :=
      (mem_stageSection (D := D) (stage := stage) (x := x)).mp hxSection
    have hxLift : (stage, x) ∈ stageLift stage E := by simp [hxE]
    exact (Finset.disjoint_left.mp hDisjoint) hxD hxLift

/-- Replace exactly one stage section of a staged set. -/
def replaceStage {r b : Nat} (D : Finset (StagedProductVertex r b))
    (stage : Fin r) (K : Finset (ProductVertex b)) :
    Finset (StagedProductVertex r b) :=
  (D.filter fun vertex => vertex.1 ≠ stage) ∪ stageLift stage K

@[simp] theorem stageSection_replace_same {r b : Nat}
    (D : Finset (StagedProductVertex r b)) (stage : Fin r)
    (K : Finset (ProductVertex b)) :
    stageSection (replaceStage D stage K) stage = K := by
  classical
  ext x
  simp [replaceStage]

theorem stageSection_replace_other {r b : Nat}
    (D : Finset (StagedProductVertex r b)) (stage other : Fin r)
    (K : Finset (ProductVertex b)) (hne : other ≠ stage) :
    stageSection (replaceStage D stage K) other = stageSection D other := by
  classical
  ext x
  simp [replaceStage, hne]

theorem replaceStage_subset {r b : Nat}
    (D : Finset (StagedProductVertex r b)) (stage : Fin r)
    {K : Finset (ProductVertex b)} (hK : K ⊆ stageSection D stage) :
    replaceStage D stage K ⊆ D := by
  classical
  rintro ⟨other, x⟩ hx
  simp only [replaceStage, Finset.mem_union, Finset.mem_filter,
    mem_stageLift] at hx
  rcases hx with ⟨hxD, _⟩ | ⟨hother, hxK⟩
  · exact hxD
  · subst other
    exact (mem_stageSection (D := D) (stage := stage) (x := x)).mp
      (hK hxK)

/-- Minimal hitting sets of a disjoint union factor exactly into minimal
hitting sets of every stage. -/
theorem minimal_hits_stagedProductFamily_iff {r b : Nat}
    (D : Finset (StagedProductVertex r b)) :
    Minimal (Hits (stagedProductFamily r b)) D ↔
      ∀ stage : Fin r,
        Minimal (Hits (switchProductFamily b)) (stageSection D stage) := by
  classical
  constructor
  · intro hMinimal stage
    have hSections := (hits_stagedProductFamily_iff D).mp hMinimal.1
    refine ⟨hSections stage, ?_⟩
    intro K hKHits hKsub
    let D' := replaceStage D stage K
    have hD'Hits : Hits (stagedProductFamily r b) D' :=
      (hits_stagedProductFamily_iff D').mpr fun other => by
        by_cases hEq : other = stage
        · subst other
          simpa [D'] using hKHits
        · rw [show stageSection D' other = stageSection D other by
            exact stageSection_replace_other D stage other K hEq]
          exact hSections other
    have hD'sub : D' ⊆ D := replaceStage_subset D stage hKsub
    have hDsub : D ⊆ D' := hMinimal.2 hD'Hits hD'sub
    intro x hxSection
    have hxD : (stage, x) ∈ D :=
      (mem_stageSection (D := D) (stage := stage) (x := x)).mp hxSection
    have hxD' := hDsub hxD
    simp [D', replaceStage] at hxD'
    exact hxD'
  · intro hSections
    refine ⟨(hits_stagedProductFamily_iff D).mpr fun stage =>
      (hSections stage).1, ?_⟩
    intro K hKHits hKD
    have hKSections := (hits_stagedProductFamily_iff K).mp hKHits
    intro vertex hvertexD
    have hsectionSub : stageSection K vertex.1 ⊆
        stageSection D vertex.1 := by
      intro x hxK
      apply (mem_stageSection (D := D) (stage := vertex.1) (x := x)).mpr
      exact hKD ((mem_stageSection (D := K) (stage := vertex.1) (x := x)).mp hxK)
    have hback := (hSections vertex.1).2 (hKSections vertex.1) hsectionSub
    apply (mem_stageSection (D := K) (stage := vertex.1)
      (x := vertex.2)).mp
    exact hback ((mem_stageSection (D := D) (stage := vertex.1)
      (x := vertex.2)).mpr hvertexD)

/-- The outer blocker can therefore be described without recomputing any
global transversals: each section is one of the `4b` component blockers. -/
theorem mem_blocker_stagedProductFamily_iff {r b : Nat}
    (D : Finset (StagedProductVertex r b)) :
    D ∈ blocker (stagedProductFamily r b) ↔
      ∀ stage : Fin r, stageSection D stage ∈ switchProductDual b := by
  rw [mem_blocker, minimal_hits_stagedProductFamily_iff]
  exact forall_congr' fun stage => by rw [← mem_blocker, switchProduct_blocker_eq]

/-- Assemble tagged, pairwise-disjoint stage sections. -/
def assembleStages {r b : Nat} (parts : Fin r → Finset (ProductVertex b)) :
    Finset (StagedProductVertex r b) :=
  Finset.univ.biUnion fun stage => stageLift stage (parts stage)

@[simp] theorem stageSection_assembleStages {r b : Nat}
    (parts : Fin r → Finset (ProductVertex b)) (stage : Fin r) :
    stageSection (assembleStages parts) stage = parts stage := by
  classical
  ext x
  simp [assembleStages]

@[simp] theorem assembleStages_sections {r b : Nat}
    (D : Finset (StagedProductVertex r b)) :
    assembleStages (fun stage => stageSection D stage) = D := by
  classical
  ext vertex
  rcases vertex with ⟨stage, x⟩
  simp [assembleStages]

/-- The outer blocker is canonically equivalent to an independent component
blocker choice at every stage. -/
noncomputable def stagedBlockerEquiv (r b : Nat) :
    {D // D ∈ blocker (stagedProductFamily r b)} ≃
      (Fin r → {E // E ∈ switchProductDual b}) where
  toFun D stage :=
    ⟨stageSection D.1 stage,
      (mem_blocker_stagedProductFamily_iff D.1).mp D.2 stage⟩
  invFun parts :=
    ⟨assembleStages fun stage => (parts stage).1,
      (mem_blocker_stagedProductFamily_iff _).mpr fun stage => by
        rw [stageSection_assembleStages]
        exact (parts stage).2⟩
  left_inv D := by
    apply Subtype.ext
    exact assembleStages_sections D.1
  right_inv parts := by
    funext stage
    apply Subtype.ext
    exact stageSection_assembleStages (fun index => (parts index).1) stage

/-- Exact output size of the `r`-stage product: one of `4b` component
blockers is selected independently at every stage. -/
theorem stagedProduct_blocker_card (r b : Nat) :
    (blocker (stagedProductFamily r b)).card = (4 * b) ^ r := by
  classical
  calc
    (blocker (stagedProductFamily r b)).card =
        Fintype.card {D // D ∈ blocker (stagedProductFamily r b)} :=
      (Fintype.card_coe (blocker (stagedProductFamily r b))).symm
    _ = Fintype.card (Fin r → {E // E ∈ switchProductDual b}) :=
      Fintype.card_congr (stagedBlockerEquiv r b)
    _ = (4 * b) ^ r := by simp [switchProductDual_card]

/-- The canonical selected edge in one outer stage. -/
noncomputable def selectedStagedEdge {r b : Nat} (stage : Fin r) :
    Finset (StagedProductVertex r b) :=
  stageLift stage (selectedProductEdge b)

/-- A stage-local cover region generated by an arbitrary component edge and
one distinguished universal point. -/
noncomputable def stagedCoverRegion {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool) :
    Finset (StagedProductVertex r b) :=
  let point : StagedProductVertex r b := (stage, (block, Sum.inr 0))
  insert point ((Finset.univ \ prior (selectedStagedEdge stage) point) \
    stageLift stage (switchProductEdge choice))

theorem selectedStagedEdge_mem_family {r b : Nat} (stage : Fin r) :
    selectedStagedEdge stage ∈ stagedProductFamily r b := by
  exact (mem_stagedProductFamily (A := selectedStagedEdge stage)).mpr
    ⟨stage, selectedProductEdge b, selectedProductEdge_mem_family b, rfl⟩

theorem stagedCoverRegion_mem_strongCover {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool) :
    stagedCoverRegion stage block choice ∈
      strongMemberFullCover (stagedProductFamily r b)
        (selectedStagedEdge stage) := by
  classical
  simp only [strongMemberFullCover, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨stageLift stage (switchProductEdge choice),
    (mem_stagedProductFamily (A := _)).mpr
      ⟨stage, switchProductEdge choice,
        switchProductEdge_mem_family choice, rfl⟩,
    (stage, (block, Sum.inr 0)), ?_, rfl⟩
  simp [selectedStagedEdge, selectedProductEdge]

@[simp] theorem universal_mem_stagedCoverRegion_iff {r b : Nat}
    (stage other : Fin r) (block index : Fin b) (point : Fin 3)
    (choice : Fin b → Bool) :
    (other, (index, Sum.inr point)) ∈ stagedCoverRegion stage block choice ↔
      other ≠ stage ∨ (other = stage ∧ index = block ∧ point = 0) := by
  classical
  simp [stagedCoverRegion, prior, selectedStagedEdge, selectedProductEdge]
  by_cases hstage : other = stage <;> simp [hstage]

@[simp] theorem trueSwitch_mem_stagedCoverRegion_iff {r b : Nat}
    (stage : Fin r) (block index : Fin b) (choice : Fin b → Bool) :
    (stage, (index, Sum.inl true)) ∈ stagedCoverRegion stage block choice ↔
      choice index = false := by
  classical
  simp [stagedCoverRegion, prior, selectedStagedEdge, selectedProductEdge]

theorem stagedCoverRegion_injective {r b : Nat} (stage : Fin r) :
    Function.Injective (fun code : Fin b × (Fin b → Bool) =>
      stagedCoverRegion stage code.1 code.2) := by
  classical
  rintro ⟨block, choice⟩ ⟨otherBlock, otherChoice⟩ hRegions
  have hBlockMem := Finset.ext_iff.mp hRegions
    (stage, (block, Sum.inr 0))
  have hBlock : block = otherBlock := by
    simpa using hBlockMem
  subst otherBlock
  have hChoice : choice = otherChoice := by
    funext index
    have hSwitch := Finset.ext_iff.mp hRegions
      (stage, (index, Sum.inl true))
    simp only [trueSwitch_mem_stagedCoverRegion_iff] at hSwitch
    cases hLeft : choice index <;> cases hRight : otherChoice index <;>
      simp [hLeft, hRight] at hSwitch ⊢
  exact Prod.ext rfl hChoice

/-- Every untouched stage inherits at least the component's `b*2^b`
different first-step cover regions. -/
theorem strongStagedCover_card_ge {r b : Nat} (stage : Fin r) :
    b * 2 ^ b ≤
      (strongMemberFullCover (stagedProductFamily r b)
        (selectedStagedEdge stage)).card := by
  classical
  let codes : Finset (Fin b × (Fin b → Bool)) := Finset.univ
  let regions := codes.image fun code =>
    stagedCoverRegion stage code.1 code.2
  have hRegions : regions ⊆
      strongMemberFullCover (stagedProductFamily r b)
        (selectedStagedEdge stage) := by
    intro region hRegion
    obtain ⟨code, _, rfl⟩ := Finset.mem_image.mp hRegion
    exact stagedCoverRegion_mem_strongCover stage code.1 code.2
  calc
    b * 2 ^ b = codes.card := by simp [codes]
    _ = regions.card := by
      exact (Finset.card_image_iff.mpr fun left _ right _ h =>
        stagedCoverRegion_injective stage h).symm
    _ ≤ _ := Finset.card_le_card hRegions

theorem untouched_mem_stagedCoverRegion {r b : Nat} (stage other : Fin r)
    (hne : other ≠ stage) (block : Fin b) (choice : Fin b → Bool)
    (x : ProductVertex b) :
    (other, x) ∈ stagedCoverRegion stage block choice := by
  classical
  rcases x with ⟨index, switch | point⟩
  · cases switch <;>
      simp [stagedCoverRegion, prior, selectedStagedEdge,
        selectedProductEdge, hne]
  · simp [stagedCoverRegion, prior, selectedStagedEdge,
      selectedProductEdge, hne]

/-- Among the component blockers, exactly the distinguished universal
singleton fits inside its generated strong-cover region. -/
theorem componentDual_stageLift_subset_stagedCoverRegion_iff {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool)
    {D : Finset (ProductVertex b)} (hD : D ∈ switchProductDual b) :
    stageLift stage D ⊆ stagedCoverRegion stage block choice ↔
      D = {(block, Sum.inr 0)} := by
  classical
  constructor
  · intro hsub
    simp only [switchProductDual, Finset.mem_union] at hD
    rcases hD with hUniversal | hSwitch
    · obtain ⟨⟨otherBlock, point⟩, _, rfl⟩ :=
        Finset.mem_image.mp hUniversal
      have hmem := hsub (show
        (stage, (otherBlock, Sum.inr point)) ∈
          stageLift stage ({(otherBlock, Sum.inr point)} :
            Finset (ProductVertex b)) by simp)
      simp only [universal_mem_stagedCoverRegion_iff] at hmem
      rcases hmem with hne | ⟨_, hblock, hpoint⟩
      · exact (hne rfl).elim
      · subst otherBlock
        subst point
        rfl
    · obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hSwitch
      have htrue := hsub (show
        (stage, (index, Sum.inl true)) ∈ stageLift stage (switchBlocker index) by
          simp [switchBlocker])
      have hchoice : choice index = false :=
        (trueSwitch_mem_stagedCoverRegion_iff stage block index choice).mp htrue
      have hfalse := hsub (show
        (stage, (index, Sum.inl false)) ∈ stageLift stage (switchBlocker index) by
          simp [switchBlocker])
      simp [stagedCoverRegion, prior, selectedStagedEdge,
        selectedProductEdge, hchoice] at hfalse
  · rintro rfl
    rintro ⟨other, x⟩ hvertex
    obtain ⟨hother, hx⟩ :=
      (mem_stageLift stage ({(block, Sum.inr 0)} :
        Finset (ProductVertex b)) other x).mp hvertex
    subst other
    have hxEq : x = (block, Sum.inr 0) := by simpa using hx
    subst x
    simp [stagedCoverRegion]

/-- Filtering an outer blocker by one stage region fixes exactly that stage's
component blocker and imposes no condition on any untouched stage. -/
theorem blocker_subset_stagedCoverRegion_iff {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool)
    {D : Finset (StagedProductVertex r b)}
    (hD : D ∈ blocker (stagedProductFamily r b)) :
    D ⊆ stagedCoverRegion stage block choice ↔
      stageSection D stage = {(block, Sum.inr 0)} := by
  classical
  have hSectionDual : stageSection D stage ∈ switchProductDual b :=
    (mem_blocker_stagedProductFamily_iff D).mp hD stage
  constructor
  · intro hsub
    apply (componentDual_stageLift_subset_stagedCoverRegion_iff
      stage block choice hSectionDual).mp
    rintro ⟨other, x⟩ hvertex
    obtain ⟨hother, hxSection⟩ :=
      (mem_stageLift stage (stageSection D stage) other x).mp hvertex
    subst other
    exact hsub ((mem_stageSection (D := D) (stage := stage) (x := x)).mp
      hxSection)
  · intro hSection vertex hvertexD
    obtain ⟨other, x⟩ := vertex
    by_cases hEq : other = stage
    · subst other
      have hxSection : x ∈ stageSection D stage :=
        (mem_stageSection (D := D) (stage := stage) (x := x)).mpr hvertexD
      rw [hSection] at hxSection
      have hx : x = (block, Sum.inr 0) := by simpa using hxSection
      subst x
      simp [stagedCoverRegion]
    · exact untouched_mem_stagedCoverRegion stage other hEq block choice x

theorem mem_filterWithin_blocker_stagedCoverRegion_iff {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool)
    (D : Finset (StagedProductVertex r b)) :
    D ∈ filterWithin (blocker (stagedProductFamily r b))
        (stagedCoverRegion stage block choice) ↔
      D ∈ blocker (stagedProductFamily r b) ∧
        stageSection D stage = {(block, Sum.inr 0)} := by
  classical
  simp only [filterWithin, Finset.mem_filter]
  constructor
  · rintro ⟨hD, hsub⟩
    exact ⟨hD, (blocker_subset_stagedCoverRegion_iff
      stage block choice hD).mp hsub⟩
  · rintro ⟨hD, hSection⟩
    exact ⟨hD, (blocker_subset_stagedCoverRegion_iff
      stage block choice hD).mpr hSection⟩

/-- Reassemble a staged blocker after fixing one stage and independently
choosing a blocker on every remaining stage. -/
def assembleWithFixedStage {r b : Nat} (stage : Fin r)
    (fixed : Finset (ProductVertex b))
    (parts : {other : Fin r // other ≠ stage} →
      Finset (ProductVertex b)) : Finset (StagedProductVertex r b) :=
  assembleStages fun other =>
    if h : other = stage then fixed else parts ⟨other, h⟩

/-- A filtered outer blocker is exactly an independent blocker choice on the
remaining stages. -/
noncomputable def filteredStagedBlockerEquiv {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool) :
    {D // D ∈ filterWithin (blocker (stagedProductFamily r b))
      (stagedCoverRegion stage block choice)} ≃
      ({other : Fin r // other ≠ stage} →
        {E // E ∈ switchProductDual b}) where
  toFun D other :=
    ⟨stageSection D.1 other.1,
      (mem_blocker_stagedProductFamily_iff D.1).mp
        ((mem_filterWithin_blocker_stagedCoverRegion_iff
          stage block choice D.1).mp D.2).1 other.1⟩
  invFun parts := by
    let fixed : Finset (ProductVertex b) := {(block, Sum.inr 0)}
    let candidate := assembleWithFixedStage stage fixed
      (fun other => (parts other).1)
    have hBlocker : candidate ∈ blocker (stagedProductFamily r b) :=
      (mem_blocker_stagedProductFamily_iff candidate).mpr fun other => by
        by_cases hEq : other = stage
        · subst other
          simp [candidate, assembleWithFixedStage, fixed,
            switchProductDual, universalBlockers]
        · simp [candidate, assembleWithFixedStage, hEq, (parts ⟨other, hEq⟩).2]
    refine ⟨candidate,
      (mem_filterWithin_blocker_stagedCoverRegion_iff
        stage block choice candidate).mpr ⟨hBlocker, ?_⟩⟩
    simp [candidate, assembleWithFixedStage, fixed]
  left_inv D := by
    apply Subtype.ext
    rw [← assembleStages_sections D.1]
    apply congrArg assembleStages
    funext other
    by_cases hEq : other = stage
    · subst other
      simp [
        ((mem_filterWithin_blocker_stagedCoverRegion_iff
          stage block choice D.1).mp D.2).2]
    · simp [hEq]
  right_inv parts := by
    funext other
    apply Subtype.ext
    simp [assembleWithFixedStage, other.2]

theorem filterWithin_stagedCoverRegion_card (stage : Fin r) (block : Fin b)
    (choice : Fin b → Bool) :
    (filterWithin (blocker (stagedProductFamily r b))
      (stagedCoverRegion stage block choice)).card = (4 * b) ^ (r - 1) := by
  classical
  calc
    (filterWithin (blocker (stagedProductFamily r b))
        (stagedCoverRegion stage block choice)).card =
        Fintype.card {D // D ∈ filterWithin
          (blocker (stagedProductFamily r b))
          (stagedCoverRegion stage block choice)} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ({other : Fin r // other ≠ stage} →
        {E // E ∈ switchProductDual b}) :=
      Fintype.card_congr (filteredStagedBlockerEquiv stage block choice)
    _ = (4 * b) ^ (r - 1) := by
      simp [switchProductDual_card, Fintype.card_subtype_compl]

/-- An edge in an untouched stage is wholly retained by a stage-local cover
region. -/
theorem stageLift_inter_stagedCoverRegion_of_ne {r b : Nat}
    (stage other : Fin r) (hne : other ≠ stage) (block : Fin b)
    (choice : Fin b → Bool) (E : Finset (ProductVertex b)) :
    stageLift other E ∩ stagedCoverRegion stage block choice =
      stageLift other E := by
  classical
  apply Finset.inter_eq_left.mpr
  rintro ⟨actualStage, x⟩ hvertex
  obtain ⟨hother, hxE⟩ :=
    (mem_stageLift other E actualStage x).mp hvertex
  subst actualStage
  exact untouched_mem_stagedCoverRegion stage other hne block choice x

/-- The edge that generated a cover region meets that region in exactly its
distinguished universal point. -/
theorem generatingEdge_inter_stagedCoverRegion {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool) :
    stageLift stage (switchProductEdge choice) ∩
        stagedCoverRegion stage block choice =
      {(stage, (block, Sum.inr 0))} := by
  classical
  ext vertex
  rcases vertex with ⟨other, ⟨index, switch | point⟩⟩
  · cases switch <;>
      simp [stagedCoverRegion, prior, selectedStagedEdge,
        selectedProductEdge]
  · simp [stagedCoverRegion, prior, selectedStagedEdge,
      selectedProductEdge]

theorem universal_mem_of_mem_switchProductFamily {b : Nat}
    {E : Finset (ProductVertex b)} (hE : E ∈ switchProductFamily b)
    (block : Fin b) (point : Fin 3) :
    (block, Sum.inr point) ∈ E := by
  classical
  obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hE
  simp

theorem switchProductFamily_isClutter (b : Nat) :
    IsClutter (switchProductFamily b) := by
  classical
  intro A hA B hB hAB
  obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨other, _, rfl⟩ := Finset.mem_image.mp hB
  have hChoice : choice = other := by
    funext block
    have hmem := hAB (show
      (block, Sum.inl (choice block)) ∈ switchProductEdge choice by simp)
    simpa using hmem
  subst other
  exact Finset.Subset.rfl

/-- Inclusion-minimal members of a displayed finite family. -/
def minimalMembers {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter fun A => ∀ B ∈ F, B ⊆ A → A ⊆ B

/-- The normalized projection used in the hybrid recursion. -/
def projectWithin {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  minimalMembers (F.image fun A => A ∩ S)

noncomputable def stagedProductFamilyExcept {r b : Nat} (stage : Fin r) :
    Finset (Finset (StagedProductVertex r b)) :=
  (Finset.univ.erase stage).biUnion fun other =>
    (switchProductFamily b).image (stageLift other)

@[simp] theorem mem_stagedProductFamilyExcept {r b : Nat} (stage : Fin r)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ stagedProductFamilyExcept stage ↔
      ∃ other : Fin r, other ≠ stage ∧
        ∃ E ∈ switchProductFamily b, stageLift other E = A := by
  classical
  simp [stagedProductFamilyExcept]

theorem stagedProductFamilyExcept_isClutter {r b : Nat} (stage : Fin r)
    (witnessBlock : Fin b) :
    IsClutter (stagedProductFamilyExcept (b := b) stage) := by
  classical
  intro A hA B hB hAB
  obtain ⟨leftStage, hLeftNe, E, hE, rfl⟩ :=
    (mem_stagedProductFamilyExcept stage A).mp hA
  obtain ⟨rightStage, hRightNe, F, hF, rfl⟩ :=
    (mem_stagedProductFamilyExcept stage B).mp hB
  have hStage : leftStage = rightStage := by
    have hmem := hAB (show
      (leftStage, (witnessBlock, Sum.inr 0)) ∈ stageLift leftStage E by
        simp [universal_mem_of_mem_switchProductFamily hE witnessBlock 0])
    exact (mem_stageLift rightStage F leftStage
      (witnessBlock, Sum.inr 0)).mp hmem |>.1
  subst rightStage
  have hEF : E ⊆ F := by
    intro x hxE
    have hx := hAB (show (leftStage, x) ∈ stageLift leftStage E by simp [hxE])
    simpa using hx
  have hFE : F ⊆ E := switchProductFamily_isClutter b E hE F hF hEF
  intro vertex hvertex
  obtain ⟨hstage, hxF⟩ :=
    (mem_stageLift leftStage F vertex.1 vertex.2).mp hvertex
  exact (mem_stageLift leftStage E vertex.1 vertex.2).mpr
    ⟨hstage, hFE hxF⟩

noncomputable def rawStagedProjection {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool) :
    Finset (Finset (StagedProductVertex r b)) :=
  (stagedProductFamily r b).image fun E =>
    E ∩ stagedCoverRegion stage block choice

theorem mem_rawStagedProjection_iff {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ rawStagedProjection stage block choice ↔
      (∃ E ∈ switchProductFamily b,
        stageLift stage E ∩ stagedCoverRegion stage block choice = A) ∨
      A ∈ stagedProductFamilyExcept stage := by
  classical
  constructor
  · intro hA
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨sourceStage, E, hE, rfl⟩ :=
      (mem_stagedProductFamily (A := source)).mp hSource
    by_cases hEq : sourceStage = stage
    · subst sourceStage
      exact Or.inl ⟨E, hE, rfl⟩
    · exact Or.inr ((mem_stagedProductFamilyExcept stage _).mpr
        ⟨sourceStage, hEq, E, hE,
          (stageLift_inter_stagedCoverRegion_of_ne
            stage sourceStage hEq block choice E).symm⟩)
  · rintro (⟨E, hE, rfl⟩ | hA)
    · exact Finset.mem_image.mpr
        ⟨stageLift stage E,
          (mem_stagedProductFamily (A := stageLift stage E)).mpr
            ⟨stage, E, hE, rfl⟩, rfl⟩
    · obtain ⟨other, hne, E, hE, rfl⟩ :=
        (mem_stagedProductFamilyExcept stage A).mp hA
      exact Finset.mem_image.mpr
        ⟨stageLift other E,
          (mem_stagedProductFamily (A := stageLift other E)).mpr
            ⟨other, E, hE, rfl⟩,
          stageLift_inter_stagedCoverRegion_of_ne
            stage other hne block choice E⟩

theorem singleton_mem_rawStagedProjection {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool) :
    ({(stage, (block, Sum.inr 0))} :
      Finset (StagedProductVertex r b)) ∈
        rawStagedProjection stage block choice := by
  exact (mem_rawStagedProjection_iff stage block choice _).mpr <|
    Or.inl ⟨switchProductEdge choice, switchProductEdge_mem_family choice,
      generatingEdge_inter_stagedCoverRegion stage block choice⟩

theorem singleton_subset_processed_projection {r b : Nat} (stage : Fin r)
    (block : Fin b) (choice : Fin b → Bool)
    {E : Finset (ProductVertex b)} (hE : E ∈ switchProductFamily b) :
    ({(stage, (block, Sum.inr 0))} :
        Finset (StagedProductVertex r b)) ⊆
      stageLift stage E ∩ stagedCoverRegion stage block choice := by
  intro vertex hvertex
  have hvertexEq : vertex = (stage, (block, Sum.inr 0)) := by
    simpa using hvertex
  subst vertex
  exact Finset.mem_inter.mpr ⟨by
    simp [universal_mem_of_mem_switchProductFamily hE block 0], by
    simp [stagedCoverRegion]⟩

theorem singleton_mem_minimalMembers_rawStagedProjection {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool) :
    ({(stage, (block, Sum.inr 0))} :
        Finset (StagedProductVertex r b)) ∈
      minimalMembers (rawStagedProjection stage block choice) := by
  refine Finset.mem_filter.mpr ⟨
    singleton_mem_rawStagedProjection stage block choice, ?_⟩
  intro B hB hBsub
  rcases (mem_rawStagedProjection_iff stage block choice B).mp hB with
      ⟨E, hE, rfl⟩ | hBexcept
  · exact singleton_subset_processed_projection stage block choice hE
  · obtain ⟨other, hne, E, hE, rfl⟩ :=
      (mem_stagedProductFamilyExcept stage B).mp hBexcept
    have huniversal :
        (other, (block, Sum.inr 0)) ∈ stageLift other E := by
      simp [universal_mem_of_mem_switchProductFamily hE block 0]
    have hsingleton := hBsub huniversal
    have heq :
        (other, (block, Sum.inr (0 : Fin 3))) =
          (stage, (block, Sum.inr (0 : Fin 3))) :=
      Finset.mem_singleton.mp hsingleton
    exact (hne (congrArg Prod.fst heq)).elim

theorem mem_minimalMembers_rawStagedProjection_of_mem_except {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool)
    {A : Finset (StagedProductVertex r b)}
    (hA : A ∈ stagedProductFamilyExcept stage) :
    A ∈ minimalMembers (rawStagedProjection stage block choice) := by
  refine Finset.mem_filter.mpr ⟨
    (mem_rawStagedProjection_iff stage block choice A).mpr (Or.inr hA), ?_⟩
  intro B hB hBsub
  rcases (mem_rawStagedProjection_iff stage block choice B).mp hB with
      ⟨E, hE, rfl⟩ | hBexcept
  · obtain ⟨other, hne, F, hF, rfl⟩ :=
      (mem_stagedProductFamilyExcept stage A).mp hA
    have hpointB :
        (stage, (block, Sum.inr 0)) ∈
          stageLift stage E ∩ stagedCoverRegion stage block choice :=
      singleton_subset_processed_projection stage block choice hE (by simp)
    have hpointA := hBsub hpointB
    have hstage :=
      (mem_stageLift other F stage (block, Sum.inr 0)).mp hpointA |>.1
    exact (hne hstage.symm).elim
  · exact stagedProductFamilyExcept_isClutter stage block B hBexcept A hA hBsub

theorem mem_minimalMembers_rawStagedProjection_iff {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ minimalMembers (rawStagedProjection stage block choice) ↔
      A = {(stage, (block, Sum.inr 0))} ∨
      A ∈ stagedProductFamilyExcept stage := by
  constructor
  · intro hA
    have hraw := (Finset.mem_filter.mp hA).1
    rcases (mem_rawStagedProjection_iff stage block choice A).mp hraw with
        ⟨E, hE, hEq⟩ | hAexcept
    · subst A
      have hsubset := (Finset.mem_filter.mp hA).2
        {(stage, (block, Sum.inr 0))}
        (singleton_mem_rawStagedProjection stage block choice)
        (singleton_subset_processed_projection stage block choice hE)
      exact Or.inl (Finset.Subset.antisymm hsubset
        (singleton_subset_processed_projection stage block choice hE))
    · exact Or.inr hAexcept
  · rintro (rfl | hAexcept)
    · exact singleton_mem_minimalMembers_rawStagedProjection stage block choice
    · exact mem_minimalMembers_rawStagedProjection_of_mem_except
        stage block choice hAexcept

theorem projectWithin_stagedCoverRegion_eq {r b : Nat}
    (stage : Fin r) (block : Fin b) (choice : Fin b → Bool) :
    projectWithin (stagedProductFamily r b)
        (stagedCoverRegion stage block choice) =
      insert ({(stage, (block, Sum.inr 0))} :
        Finset (StagedProductVertex r b))
        (stagedProductFamilyExcept stage) := by
  classical
  ext A
  change A ∈ minimalMembers (rawStagedProjection stage block choice) ↔ _
  rw [mem_minimalMembers_rawStagedProjection_iff]
  simp [eq_comm]

/-- The universe obtained after choosing one generated region at every stage
in `processed`. -/
noncomputable def accumulatedStagedRegion {r b : Nat} (processed : Finset (Fin r))
    (blockAt : Fin r → Fin b) (choiceAt : Fin r → Fin b → Bool) :
    Finset (StagedProductVertex r b) :=
  Finset.univ.filter fun vertex =>
    ∀ stage ∈ processed,
      vertex ∈ stagedCoverRegion stage (blockAt stage) (choiceAt stage)

@[simp] theorem mem_accumulatedStagedRegion_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (vertex : StagedProductVertex r b) :
    vertex ∈ accumulatedStagedRegion processed blockAt choiceAt ↔
      ∀ stage ∈ processed,
        vertex ∈ stagedCoverRegion stage (blockAt stage) (choiceAt stage) := by
  simp [accumulatedStagedRegion]

/-- A global blocker fits the accumulated universe exactly when every
processed stage section is its distinguished singleton. -/
theorem blocker_subset_accumulatedStagedRegion_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool)
    {D : Finset (StagedProductVertex r b)}
    (hD : D ∈ blocker (stagedProductFamily r b)) :
    D ⊆ accumulatedStagedRegion processed blockAt choiceAt ↔
      ∀ stage ∈ processed,
        stageSection D stage = {(blockAt stage, Sum.inr 0)} := by
  constructor
  · intro hsub stage hstage
    apply (blocker_subset_stagedCoverRegion_iff
      stage (blockAt stage) (choiceAt stage) hD).mp
    intro vertex hvertex
    exact (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt vertex).mp (hsub hvertex) stage hstage
  · intro hsections vertex hvertex
    apply (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt vertex).mpr
    intro stage hstage
    exact (blocker_subset_stagedCoverRegion_iff
      stage (blockAt stage) (choiceAt stage) hD).mpr
        (hsections stage hstage) hvertex

theorem mem_filterWithin_blocker_accumulatedStagedRegion_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool)
    (D : Finset (StagedProductVertex r b)) :
    D ∈ filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt) ↔
      D ∈ blocker (stagedProductFamily r b) ∧
      ∀ stage ∈ processed,
        stageSection D stage = {(blockAt stage, Sum.inr 0)} := by
  simp only [filterWithin, Finset.mem_filter]
  constructor
  · rintro ⟨hD, hsub⟩
    exact ⟨hD, (blocker_subset_accumulatedStagedRegion_iff
      processed blockAt choiceAt hD).mp hsub⟩
  · rintro ⟨hD, hsections⟩
    exact ⟨hD, (blocker_subset_accumulatedStagedRegion_iff
      processed blockAt choiceAt hD).mpr hsections⟩

/-- Reassemble a staged blocker with all processed sections fixed and all
unprocessed sections independently chosen. -/
def assembleWithFixedStages {r b : Nat} (processed : Finset (Fin r))
    (blockAt : Fin r → Fin b)
    (parts : {stage : Fin r // stage ∉ processed} →
      Finset (ProductVertex b)) : Finset (StagedProductVertex r b) :=
  assembleStages fun stage =>
    if h : stage ∈ processed then {(blockAt stage, Sum.inr 0)}
    else parts ⟨stage, h⟩

/-- After any set of distinct stages has been processed, the surviving
blocker is the independent product over exactly the unprocessed stages. -/
noncomputable def filteredAccumulatedStagedBlockerEquiv {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) :
    {D // D ∈ filterWithin (blocker (stagedProductFamily r b))
      (accumulatedStagedRegion processed blockAt choiceAt)} ≃
      ({stage : Fin r // stage ∉ processed} →
        {E // E ∈ switchProductDual b}) where
  toFun D stage :=
    ⟨stageSection D.1 stage.1,
      (mem_blocker_stagedProductFamily_iff D.1).mp
        ((mem_filterWithin_blocker_accumulatedStagedRegion_iff
          processed blockAt choiceAt D.1).mp D.2).1 stage.1⟩
  invFun parts := by
    let candidate := assembleWithFixedStages processed blockAt
      (fun stage => (parts stage).1)
    have hBlocker : candidate ∈ blocker (stagedProductFamily r b) :=
      (mem_blocker_stagedProductFamily_iff candidate).mpr fun stage => by
        by_cases h : stage ∈ processed
        · simp [candidate, assembleWithFixedStages, h,
            switchProductDual, universalBlockers]
        · simp [candidate, assembleWithFixedStages, h, (parts ⟨stage, h⟩).2]
    refine ⟨candidate,
      (mem_filterWithin_blocker_accumulatedStagedRegion_iff
        processed blockAt choiceAt candidate).mpr ⟨hBlocker, ?_⟩⟩
    intro stage hstage
    simp [candidate, assembleWithFixedStages, hstage]
  left_inv D := by
    apply Subtype.ext
    rw [← assembleStages_sections D.1]
    apply congrArg assembleStages
    funext stage
    by_cases h : stage ∈ processed
    · simp [h,
        ((mem_filterWithin_blocker_accumulatedStagedRegion_iff
          processed blockAt choiceAt D.1).mp D.2).2 stage h]
    · simp [h]
  right_inv parts := by
    funext stage
    apply Subtype.ext
    simp [assembleWithFixedStages, stage.2]

theorem filterWithin_accumulatedStagedRegion_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) :
    (filterWithin (blocker (stagedProductFamily r b))
      (accumulatedStagedRegion processed blockAt choiceAt)).card =
        (4 * b) ^ (r - processed.card) := by
  classical
  calc
    (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt)).card =
        Fintype.card {D // D ∈ filterWithin
          (blocker (stagedProductFamily r b))
          (accumulatedStagedRegion processed blockAt choiceAt)} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card ({stage : Fin r // stage ∉ processed} →
        {E // E ∈ switchProductDual b}) :=
      Fintype.card_congr
        (filteredAccumulatedStagedBlockerEquiv processed blockAt choiceAt)
    _ = (4 * b) ^ (r - processed.card) := by
      simp [switchProductDual_card, Fintype.card_subtype_compl]

theorem stageLift_inter_accumulatedStagedRegion_of_mem {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) (E : Finset (ProductVertex b)) :
    stageLift stage E ∩ accumulatedStagedRegion processed blockAt choiceAt =
      stageLift stage E ∩
        stagedCoverRegion stage (blockAt stage) (choiceAt stage) := by
  ext vertex
  constructor
  · intro hvertex
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hvertex).1,
      (mem_accumulatedStagedRegion_iff
        processed blockAt choiceAt vertex).mp
          (Finset.mem_inter.mp hvertex).2 stage hstage⟩
  · intro hvertex
    obtain ⟨other, x⟩ := vertex
    have hlift := (Finset.mem_inter.mp hvertex).1
    have hregion := (Finset.mem_inter.mp hvertex).2
    refine Finset.mem_inter.mpr ⟨hlift,
      (mem_accumulatedStagedRegion_iff
        processed blockAt choiceAt (other, x)).mpr ?_⟩
    intro current hcurrent
    by_cases heq : current = stage
    · subst current
      exact hregion
    · have hother : other = stage :=
        (mem_stageLift stage E other x).mp hlift |>.1
      subst other
      exact untouched_mem_stagedCoverRegion current stage (fun h => heq h.symm)
        (blockAt current) (choiceAt current) x

theorem stageLift_inter_accumulatedStagedRegion_of_not_mem {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (E : Finset (ProductVertex b)) :
    stageLift stage E ∩ accumulatedStagedRegion processed blockAt choiceAt =
      stageLift stage E := by
  ext vertex
  constructor
  · exact fun hvertex => (Finset.mem_inter.mp hvertex).1
  · intro hvertex
    obtain ⟨other, x⟩ := vertex
    have hother : other = stage :=
      (mem_stageLift stage E other x).mp hvertex |>.1
    subst other
    refine Finset.mem_inter.mpr ⟨hvertex,
      (mem_accumulatedStagedRegion_iff
        processed blockAt choiceAt (stage, x)).mpr ?_⟩
    intro current hcurrent
    have hne : stage ≠ current := by
      intro heq
      apply hstage
      simpa [heq] using hcurrent
    exact untouched_mem_stagedCoverRegion current stage hne
      (blockAt current) (choiceAt current) x

noncomputable def stagedProductFamilyOutside {r b : Nat}
    (processed : Finset (Fin r)) :
    Finset (Finset (StagedProductVertex r b)) :=
  (Finset.univ.filter fun stage => stage ∉ processed).biUnion fun stage =>
    (switchProductFamily b).image (stageLift stage)

@[simp] theorem mem_stagedProductFamilyOutside_iff {r b : Nat}
    (processed : Finset (Fin r)) (A : Finset (StagedProductVertex r b)) :
    A ∈ stagedProductFamilyOutside processed ↔
      ∃ stage : Fin r, stage ∉ processed ∧
        ∃ E ∈ switchProductFamily b, stageLift stage E = A := by
  classical
  simp [stagedProductFamilyOutside]

noncomputable def processedSingletonFamily {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    Finset (Finset (StagedProductVertex r b)) :=
  processed.image fun stage =>
    ({(stage, (blockAt stage, Sum.inr 0))} :
      Finset (StagedProductVertex r b))

noncomputable def accumulatedPositiveNormalForm {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    Finset (Finset (StagedProductVertex r b)) :=
  processedSingletonFamily processed blockAt ∪
    stagedProductFamilyOutside processed

noncomputable def rawAccumulatedStagedProjection {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) :
    Finset (Finset (StagedProductVertex r b)) :=
  (stagedProductFamily r b).image fun E =>
    E ∩ accumulatedStagedRegion processed blockAt choiceAt

theorem mem_rawAccumulatedStagedProjection_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ rawAccumulatedStagedProjection processed blockAt choiceAt ↔
      (∃ stage ∈ processed, ∃ E ∈ switchProductFamily b,
        stageLift stage E ∩
          stagedCoverRegion stage (blockAt stage) (choiceAt stage) = A) ∨
      A ∈ stagedProductFamilyOutside processed := by
  classical
  constructor
  · intro hA
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨stage, E, hE, rfl⟩ :=
      (mem_stagedProductFamily (A := source)).mp hSource
    by_cases hstage : stage ∈ processed
    · exact Or.inl ⟨stage, hstage, E, hE,
        (stageLift_inter_accumulatedStagedRegion_of_mem
          processed blockAt choiceAt stage hstage E).symm⟩
    · exact Or.inr ((mem_stagedProductFamilyOutside_iff processed _).mpr
        ⟨stage, hstage, E, hE,
          (stageLift_inter_accumulatedStagedRegion_of_not_mem
            processed blockAt choiceAt stage hstage E).symm⟩)
  · rintro (⟨stage, hstage, E, hE, rfl⟩ | hA)
    · exact Finset.mem_image.mpr
        ⟨stageLift stage E,
          (mem_stagedProductFamily (A := stageLift stage E)).mpr
            ⟨stage, E, hE, rfl⟩,
          stageLift_inter_accumulatedStagedRegion_of_mem
            processed blockAt choiceAt stage hstage E⟩
    · obtain ⟨stage, hstage, E, hE, rfl⟩ :=
        (mem_stagedProductFamilyOutside_iff processed A).mp hA
      exact Finset.mem_image.mpr
        ⟨stageLift stage E,
          (mem_stagedProductFamily (A := stageLift stage E)).mpr
            ⟨stage, E, hE, rfl⟩,
          stageLift_inter_accumulatedStagedRegion_of_not_mem
            processed blockAt choiceAt stage hstage E⟩

@[simp] theorem mem_processedSingletonFamily_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ processedSingletonFamily processed blockAt ↔
      ∃ stage ∈ processed,
        ({(stage, (blockAt stage, Sum.inr 0))} :
          Finset (StagedProductVertex r b)) = A := by
  classical
  simp [processedSingletonFamily]

theorem processedSingleton_mem_rawAccumulatedStagedProjection {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) :
    ({(stage, (blockAt stage, Sum.inr 0))} :
        Finset (StagedProductVertex r b)) ∈
      rawAccumulatedStagedProjection processed blockAt choiceAt := by
  exact (mem_rawAccumulatedStagedProjection_iff
    processed blockAt choiceAt _).mpr <| Or.inl
      ⟨stage, hstage, switchProductEdge (choiceAt stage),
        switchProductEdge_mem_family (choiceAt stage),
        generatingEdge_inter_stagedCoverRegion
          stage (blockAt stage) (choiceAt stage)⟩

theorem stagedProductFamilyOutside_isClutter {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    IsClutter (stagedProductFamilyOutside (b := b) processed) := by
  classical
  intro A hA B hB hAB
  obtain ⟨leftStage, hLeftOut, E, hE, rfl⟩ :=
    (mem_stagedProductFamilyOutside_iff processed A).mp hA
  obtain ⟨rightStage, hRightOut, F, hF, rfl⟩ :=
    (mem_stagedProductFamilyOutside_iff processed B).mp hB
  have hStage : leftStage = rightStage := by
    have hmem := hAB (show
      (leftStage, (blockAt leftStage, Sum.inr 0)) ∈
        stageLift leftStage E by
          simp [universal_mem_of_mem_switchProductFamily
            hE (blockAt leftStage) 0])
    exact (mem_stageLift rightStage F leftStage
      (blockAt leftStage, Sum.inr 0)).mp hmem |>.1
  subst rightStage
  have hEF : E ⊆ F := by
    intro x hxE
    have hx := hAB (show (leftStage, x) ∈ stageLift leftStage E by simp [hxE])
    simpa using hx
  have hFE : F ⊆ E := switchProductFamily_isClutter b E hE F hF hEF
  intro vertex hvertex
  obtain ⟨hstage, hxF⟩ :=
    (mem_stageLift leftStage F vertex.1 vertex.2).mp hvertex
  exact (mem_stageLift leftStage E vertex.1 vertex.2).mpr
    ⟨hstage, hFE hxF⟩

theorem processedSingleton_mem_minimalMembers_rawAccumulated {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) :
    ({(stage, (blockAt stage, Sum.inr 0))} :
        Finset (StagedProductVertex r b)) ∈
      minimalMembers
        (rawAccumulatedStagedProjection processed blockAt choiceAt) := by
  refine Finset.mem_filter.mpr ⟨
    processedSingleton_mem_rawAccumulatedStagedProjection
      processed blockAt choiceAt stage hstage, ?_⟩
  intro B hB hBsub
  rcases (mem_rawAccumulatedStagedProjection_iff
      processed blockAt choiceAt B).mp hB with
      ⟨other, hother, E, hE, rfl⟩ | hBoutside
  · have hsmall := singleton_subset_processed_projection
      other (blockAt other) (choiceAt other) hE
    have hpointInSmall :
        (other, (blockAt other, Sum.inr 0)) ∈
          ({(other, (blockAt other, Sum.inr 0))} :
            Finset (StagedProductVertex r b)) := by simp
    have hpoint := hBsub (hsmall hpointInSmall)
    have heq : other = stage := congrArg Prod.fst
      (Finset.mem_singleton.mp hpoint)
    subst other
    exact hsmall
  · obtain ⟨other, hother, E, hE, rfl⟩ :=
      (mem_stagedProductFamilyOutside_iff processed B).mp hBoutside
    have huniversal :
        (other, (blockAt other, Sum.inr 0)) ∈ stageLift other E := by
      simp [universal_mem_of_mem_switchProductFamily
        hE (blockAt other) 0]
    have hpoint := hBsub huniversal
    have heq : other = stage := congrArg Prod.fst
      (Finset.mem_singleton.mp hpoint)
    subst other
    exact (hother hstage).elim

theorem mem_minimalMembers_rawAccumulated_of_mem_outside {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool)
    {A : Finset (StagedProductVertex r b)}
    (hA : A ∈ stagedProductFamilyOutside processed) :
    A ∈ minimalMembers
      (rawAccumulatedStagedProjection processed blockAt choiceAt) := by
  refine Finset.mem_filter.mpr ⟨
    (mem_rawAccumulatedStagedProjection_iff
      processed blockAt choiceAt A).mpr (Or.inr hA), ?_⟩
  intro B hB hBsub
  rcases (mem_rawAccumulatedStagedProjection_iff
      processed blockAt choiceAt B).mp hB with
      ⟨stage, hstage, E, hE, rfl⟩ | hBoutside
  · obtain ⟨other, hother, F, hF, rfl⟩ :=
      (mem_stagedProductFamilyOutside_iff processed A).mp hA
    have hpointB :
        (stage, (blockAt stage, Sum.inr 0)) ∈
          stageLift stage E ∩
            stagedCoverRegion stage (blockAt stage) (choiceAt stage) :=
      singleton_subset_processed_projection
        stage (blockAt stage) (choiceAt stage) hE (by simp)
    have hpointA := hBsub hpointB
    have heq : stage = other :=
      (mem_stageLift other F stage (blockAt stage, Sum.inr 0)).mp hpointA |>.1
    subst other
    exact (hother hstage).elim
  · exact stagedProductFamilyOutside_isClutter processed blockAt
      B hBoutside A hA hBsub

theorem mem_minimalMembers_rawAccumulated_iff {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool)
    (A : Finset (StagedProductVertex r b)) :
    A ∈ minimalMembers
        (rawAccumulatedStagedProjection processed blockAt choiceAt) ↔
      A ∈ accumulatedPositiveNormalForm processed blockAt := by
  constructor
  · intro hA
    have hraw := (Finset.mem_filter.mp hA).1
    rcases (mem_rawAccumulatedStagedProjection_iff
        processed blockAt choiceAt A).mp hraw with
        ⟨stage, hstage, E, hE, hEq⟩ | hAoutside
    · have hsmall :
          ({(stage, (blockAt stage, Sum.inr 0))} :
              Finset (StagedProductVertex r b)) ⊆ A := by
        rw [← hEq]
        exact singleton_subset_processed_projection
          stage (blockAt stage) (choiceAt stage) hE
      have hreverse := (Finset.mem_filter.mp hA).2
        {(stage, (blockAt stage, Sum.inr 0))}
        (processedSingleton_mem_rawAccumulatedStagedProjection
          processed blockAt choiceAt stage hstage) hsmall
      have hEqSingleton :
          A = {(stage, (blockAt stage, Sum.inr 0))} :=
        Finset.Subset.antisymm hreverse hsmall
      apply Finset.mem_union_left
      exact (mem_processedSingletonFamily_iff processed blockAt A).mpr
        ⟨stage, hstage, hEqSingleton.symm⟩
    · exact Finset.mem_union_right _ hAoutside
  · intro hA
    rcases Finset.mem_union.mp hA with hsingleton | houtside
    · obtain ⟨stage, hstage, hEq⟩ :=
        (mem_processedSingletonFamily_iff processed blockAt A).mp hsingleton
      rw [← hEq]
      exact processedSingleton_mem_minimalMembers_rawAccumulated
        processed blockAt choiceAt stage hstage
    · exact mem_minimalMembers_rawAccumulated_of_mem_outside
        processed blockAt choiceAt houtside

theorem projectWithin_accumulatedStagedRegion_eq {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) :
    projectWithin (stagedProductFamily r b)
        (accumulatedStagedRegion processed blockAt choiceAt) =
      accumulatedPositiveNormalForm processed blockAt := by
  ext A
  change A ∈ minimalMembers
    (rawAccumulatedStagedProjection processed blockAt choiceAt) ↔ _
  exact mem_minimalMembers_rawAccumulated_iff
    processed blockAt choiceAt A

theorem processedSingletonFamily_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    (processedSingletonFamily processed blockAt).card = processed.card := by
  classical
  rw [processedSingletonFamily, Finset.card_image_iff.mpr]
  intro left hleft right hright heq
  have hmember :
      (left, (blockAt left, Sum.inr 0)) ∈
        ({(right, (blockAt right, Sum.inr 0))} :
          Finset (StagedProductVertex r b)) := by
    change ({(left, (blockAt left, Sum.inr 0))} :
      Finset (StagedProductVertex r b)) =
        {(right, (blockAt right, Sum.inr 0))} at heq
    rw [← heq]
    simp
  exact congrArg Prod.fst (Finset.mem_singleton.mp hmember)

theorem stagedProductFamilyOutside_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    (stagedProductFamilyOutside (b := b) processed).card =
      (r - processed.card) * 2 ^ b := by
  classical
  rw [stagedProductFamilyOutside, Finset.card_biUnion]
  · have hImageCard (stage : Fin r) :
        ((switchProductFamily b).image (stageLift stage)).card = 2 ^ b := by
      rw [Finset.card_image_iff.mpr]
      · exact switchProductFamily_card b
      · intro E hE F hF hEq
        ext x
        constructor
        · intro hxE
          have hxLift : (stage, x) ∈ stageLift stage E := by simp [hxE]
          rw [hEq] at hxLift
          simpa using hxLift
        · intro hxF
          have hxLift : (stage, x) ∈ stageLift stage F := by simp [hxF]
          rw [← hEq] at hxLift
          simpa using hxLift
    calc
      (∑ stage ∈ Finset.univ.filter (fun stage : Fin r => stage ∉ processed),
          ((switchProductFamily b).image (stageLift stage)).card) =
          ∑ _stage ∈ Finset.univ.filter
            (fun stage : Fin r => stage ∉ processed), 2 ^ b := by
            apply Finset.sum_congr rfl
            intro stage hstage
            exact hImageCard stage
      _ = (Finset.univ.filter
          (fun stage : Fin r => stage ∉ processed)).card * 2 ^ b := by
            simp
      _ = (r - processed.card) * 2 ^ b := by
            congr 1
            rw [show Finset.univ.filter
                (fun stage : Fin r => stage ∉ processed) =
                Finset.univ \ processed by ext; simp,
              Finset.card_sdiff]
            simp
  · intro left hleft right hright hne
    apply Finset.disjoint_left.mpr
    intro A hAleft hAright
    obtain ⟨E, hE, hLiftLeft⟩ := Finset.mem_image.mp hAleft
    obtain ⟨F, hF, hLiftRight⟩ := Finset.mem_image.mp hAright
    have hvertexLeft :
        (left, (blockAt left, Sum.inr 0)) ∈ stageLift left E := by
      simp [universal_mem_of_mem_switchProductFamily
        hE (blockAt left) 0]
    have hvertexA :
        (left, (blockAt left, Sum.inr 0)) ∈ A := hLiftLeft ▸ hvertexLeft
    have hvertexRight :
        (left, (blockAt left, Sum.inr 0)) ∈ stageLift right F := by
      rw [hLiftRight]
      exact hvertexA
    exact hne ((mem_stageLift right F left
      (blockAt left, Sum.inr 0)).mp hvertexRight |>.1)

theorem processedSingletonFamily_disjoint_outside {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    Disjoint (processedSingletonFamily processed blockAt)
      (stagedProductFamilyOutside processed) := by
  classical
  apply Finset.disjoint_left.mpr
  intro A hAsingleton hAoutside
  obtain ⟨stage, hstage, hEq⟩ :=
    (mem_processedSingletonFamily_iff processed blockAt A).mp hAsingleton
  obtain ⟨other, hother, E, hE, hLift⟩ :=
    (mem_stagedProductFamilyOutside_iff processed A).mp hAoutside
  have hvertexA :
      (stage, (blockAt stage, Sum.inr 0)) ∈ A := by
    rw [← hEq]
    simp
  have hvertexLift :
      (stage, (blockAt stage, Sum.inr 0)) ∈ stageLift other E := by
    rw [hLift]
    exact hvertexA
  have heq : stage = other :=
    (mem_stageLift other E stage (blockAt stage, Sum.inr 0)).mp hvertexLift |>.1
  subst other
  exact hother hstage

theorem accumulatedPositiveNormalForm_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b) :
    (accumulatedPositiveNormalForm processed blockAt).card =
      processed.card + (r - processed.card) * 2 ^ b := by
  classical
  rw [accumulatedPositiveNormalForm,
    Finset.card_union_of_disjoint
      (processedSingletonFamily_disjoint_outside processed blockAt),
    processedSingletonFamily_card,
    stagedProductFamilyOutside_card processed blockAt]

theorem stageLift_injective {r b : Nat} (stage : Fin r) :
    Function.Injective (stageLift stage : Finset (ProductVertex b) →
      Finset (StagedProductVertex r b)) := by
  intro E F hEq
  ext x
  constructor
  · intro hxE
    have hxLift : (stage, x) ∈ stageLift stage E := by simp [hxE]
    rw [hEq] at hxLift
    simpa using hxLift
  · intro hxF
    have hxLift : (stage, x) ∈ stageLift stage F := by simp [hxF]
    rw [← hEq] at hxLift
    simpa using hxLift

theorem accumulatedPositive_unprocessedFiber_eq {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed) (x : ProductVertex b) :
    familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
        (stage, x) =
      (familyVertexFiber (switchProductFamily b) x).image (stageLift stage) := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨hNormal, hvertex⟩ := Finset.mem_filter.mp hA
    rcases Finset.mem_union.mp hNormal with hProcessed | hOutside
    · obtain ⟨other, hother, hEq⟩ :=
        (mem_processedSingletonFamily_iff processed blockAt A).mp hProcessed
      have hmember :
          (stage, x) ∈
            ({(other, (blockAt other, Sum.inr 0))} :
              Finset (StagedProductVertex r b)) := hEq ▸ hvertex
      have heq : stage = other := congrArg Prod.fst
        (Finset.mem_singleton.mp hmember)
      subst other
      exact (hstage hother).elim
    · obtain ⟨other, hother, E, hE, hEq⟩ :=
        (mem_stagedProductFamilyOutside_iff processed A).mp hOutside
      have hLiftVertex : (stage, x) ∈ stageLift other E := hEq ▸ hvertex
      have heq : stage = other := (mem_stageLift other E stage x).mp hLiftVertex |>.1
      subst other
      exact Finset.mem_image.mpr ⟨E,
        Finset.mem_filter.mpr ⟨hE, by simpa using hLiftVertex⟩, hEq⟩
  · intro hA
    obtain ⟨E, hEFiber, hEq⟩ := Finset.mem_image.mp hA
    obtain ⟨hE, hxE⟩ := Finset.mem_filter.mp hEFiber
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_union_right _
      ((mem_stagedProductFamilyOutside_iff processed A).mpr
        ⟨stage, hstage, E, hE, hEq⟩), ?_⟩
    rw [← hEq]
    simpa using hxE

theorem accumulatedPositive_unprocessedSwitchFiber_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (value : Bool) :
    (familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
      (stage, (block, Sum.inl value))).card = 2 ^ (b - 1) := by
  classical
  rw [accumulatedPositive_unprocessedFiber_eq
      processed blockAt stage hstage,
    Finset.card_image_iff.mpr fun left _ right _ hEq =>
      stageLift_injective stage hEq,
    switchProduct_switchFiber_card]

theorem accumulatedPositive_unprocessedUniversalFiber_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (point : Fin 3) :
    (familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
      (stage, (block, Sum.inr point))).card = 2 ^ b := by
  classical
  rw [accumulatedPositive_unprocessedFiber_eq
      processed blockAt stage hstage,
    Finset.card_image_iff.mpr fun left _ right _ hEq =>
      stageLift_injective stage hEq,
    switchProduct_universalFiber_card]

theorem accumulatedPositive_processedFiber_eq {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed) :
    familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
        (stage, (blockAt stage, Sum.inr 0)) =
      {({(stage, (blockAt stage, Sum.inr 0))} :
        Finset (StagedProductVertex r b))} := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨hNormal, hvertex⟩ := Finset.mem_filter.mp hA
    rcases Finset.mem_union.mp hNormal with hProcessed | hOutside
    · obtain ⟨other, hother, hEq⟩ :=
        (mem_processedSingletonFamily_iff processed blockAt A).mp hProcessed
      have hmember :
          (stage, (blockAt stage, Sum.inr 0)) ∈
            ({(other, (blockAt other, Sum.inr 0))} :
              Finset (StagedProductVertex r b)) := hEq ▸ hvertex
      have heq : stage = other := congrArg Prod.fst
        (Finset.mem_singleton.mp hmember)
      subst other
      exact Finset.mem_singleton.mpr hEq.symm
    · obtain ⟨other, hother, E, hE, hEq⟩ :=
        (mem_stagedProductFamilyOutside_iff processed A).mp hOutside
      have hLiftVertex :
          (stage, (blockAt stage, Sum.inr 0)) ∈ stageLift other E :=
        hEq ▸ hvertex
      have heq : stage = other :=
        (mem_stageLift other E stage (blockAt stage, Sum.inr 0)).mp
          hLiftVertex |>.1
      subst other
      exact (hother hstage).elim
  · intro hA
    have hEq := Finset.mem_singleton.mp hA
    subst A
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_union_left _
      ((mem_processedSingletonFamily_iff processed blockAt _).mpr
        ⟨stage, hstage, rfl⟩), by simp⟩

theorem accumulatedPositive_processedFiber_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed) :
    (familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
      (stage, (blockAt stage, Sum.inr 0))).card = 1 := by
  rw [accumulatedPositive_processedFiber_eq processed blockAt stage hstage]
  simp

/-- Fixing one value of an arbitrary finite function leaves a free function on
the complement of that coordinate. -/
def fixedFunctionEquiv {ι β : Type*} [DecidableEq ι]
    (index : ι) (value : β) :
    {f : ι → β // f index = value} ≃
      ({other : ι // other ≠ index} → β) where
  toFun f other := f.1 other.1
  invFun parts :=
    ⟨fun other => if h : other = index then value else parts ⟨other, h⟩, by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext other
    by_cases h : other = index
    · subst other
      simp [f.2]
    · simp [h]
  right_inv parts := by
    funext other
    simp [other.2]

def dualMemberSubtype {b : Nat} (vertex : ProductVertex b) :
    {E // E ∈ switchProductDual b} :=
  ⟨dualMemberForVertex vertex,
    ((mem_switchProductDual_and_vertex_iff
      vertex (dualMemberForVertex vertex)).mpr rfl).1⟩

/-- Under the accumulated blocker product equivalence, requiring a vertex at
an unprocessed stage is exactly the requirement that one function coordinate
equal that vertex's unique component blocker. -/
noncomputable def filteredAccumulatedVertexFiberToFixedEquiv {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (vertex : ProductVertex b) :
    {D // D ∈ familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex)} ≃
      {parts : ({other : Fin r // other ∉ processed} →
          {E // E ∈ switchProductDual b}) //
        parts ⟨stage, hstage⟩ = dualMemberSubtype vertex} where
  toFun D := by
    have hD := (Finset.mem_filter.mp D.2).1
    have hvertex := (Finset.mem_filter.mp D.2).2
    let base : {K // K ∈ filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt)} := ⟨D.1, hD⟩
    let parts := filteredAccumulatedStagedBlockerEquiv
      processed blockAt choiceAt base
    refine ⟨parts, ?_⟩
    apply Subtype.ext
    exact (mem_switchProductDual_and_vertex_iff vertex
      (stageSection D.1 stage)).mp ⟨parts ⟨stage, hstage⟩ |>.2,
        (mem_stageSection (D := D.1) (stage := stage)
          (x := vertex)).mpr hvertex⟩
  invFun parts := by
    let base := (filteredAccumulatedStagedBlockerEquiv
      processed blockAt choiceAt).symm parts.1
    refine ⟨base.1, Finset.mem_filter.mpr ⟨base.2, ?_⟩⟩
    apply (mem_stageSection (D := base.1) (stage := stage)
      (x := vertex)).mp
    have hparts := (filteredAccumulatedStagedBlockerEquiv
      processed blockAt choiceAt).apply_symm_apply parts.1
    have hsection : stageSection base.1 stage =
        (parts.1 ⟨stage, hstage⟩).1 := by
      exact congrArg (fun f => (f ⟨stage, hstage⟩).1) hparts
    rw [hsection, parts.2]
    exact ((mem_switchProductDual_and_vertex_iff
      vertex (dualMemberForVertex vertex)).mpr rfl).2
  left_inv D := by
    apply Subtype.ext
    change ((filteredAccumulatedStagedBlockerEquiv
      processed blockAt choiceAt).symm
        ((filteredAccumulatedStagedBlockerEquiv
          processed blockAt choiceAt)
            ⟨D.1, (Finset.mem_filter.mp D.2).1⟩)).1 = D.1
    exact congrArg Subtype.val
      ((filteredAccumulatedStagedBlockerEquiv
        processed blockAt choiceAt).symm_apply_apply
          ⟨D.1, (Finset.mem_filter.mp D.2).1⟩)
  right_inv parts := by
    apply Subtype.ext
    exact (filteredAccumulatedStagedBlockerEquiv
      processed blockAt choiceAt).apply_symm_apply parts.1

noncomputable def filteredAccumulatedVertexFiberEquiv {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (vertex : ProductVertex b) :
    {D // D ∈ familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex)} ≃
      ({other : {current : Fin r // current ∉ processed} //
          other ≠ (⟨stage, hstage⟩ :
            {current : Fin r // current ∉ processed})} →
        {E // E ∈ switchProductDual b}) :=
  (filteredAccumulatedVertexFiberToFixedEquiv
    processed blockAt choiceAt stage hstage vertex).trans
      (fixedFunctionEquiv
        (⟨stage, hstage⟩ : {current : Fin r // current ∉ processed})
        (dualMemberSubtype vertex))

theorem filteredAccumulated_unprocessedFiber_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (vertex : ProductVertex b) :
    (familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex)).card =
        (4 * b) ^ (r - processed.card - 1) := by
  classical
  calc
    (familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex)).card =
        Fintype.card {D // D ∈ familyVertexFiber
          (filterWithin (blocker (stagedProductFamily r b))
            (accumulatedStagedRegion processed blockAt choiceAt))
          (stage, vertex)} := (Fintype.card_coe _).symm
    _ = Fintype.card
        ({other : {current : Fin r // current ∉ processed} //
            other ≠ (⟨stage, hstage⟩ :
              {current : Fin r // current ∉ processed})} →
          {E // E ∈ switchProductDual b}) :=
      Fintype.card_congr (filteredAccumulatedVertexFiberEquiv
        processed blockAt choiceAt stage hstage vertex)
    _ = (4 * b) ^ (r - processed.card - 1) := by
      simp [switchProductDual_card, Fintype.card_subtype_compl]

theorem filteredAccumulated_processedFiber_eq {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) :
    familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, (blockAt stage, Sum.inr 0)) =
        filterWithin (blocker (stagedProductFamily r b))
          (accumulatedStagedRegion processed blockAt choiceAt) := by
  ext D
  constructor
  · exact fun hD => (Finset.mem_filter.mp hD).1
  · intro hD
    apply Finset.mem_filter.mpr
    refine ⟨hD, (mem_stageSection (D := D) (stage := stage)
      (x := (blockAt stage, Sum.inr 0))).mp ?_⟩
    have hsection :=
      ((mem_filterWithin_blocker_accumulatedStagedRegion_iff
        processed blockAt choiceAt D).mp hD).2 stage hstage
    rw [hsection]
    simp

theorem filteredAccumulated_processedFiber_card {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) :
    (familyVertexFiber
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, (blockAt stage, Sum.inr 0))).card =
        (4 * b) ^ (r - processed.card) := by
  rw [filteredAccumulated_processedFiber_eq
      processed blockAt choiceAt stage hstage,
    filterWithin_accumulatedStagedRegion_card]

/-- Relative incidence used by the frequency branch of the dualization
recursion. -/
noncomputable def familyFrequency {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (vertex : α) : ℝ :=
  (familyVertexFiber F vertex).card / F.card

theorem accumulatedPositive_unprocessedSwitch_frequency {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (value : Bool) :
    familyFrequency (accumulatedPositiveNormalForm processed blockAt)
      (stage, (block, Sum.inl value)) =
        ((2 ^ (b - 1) : Nat) : ℝ) /
          ((processed.card + (r - processed.card) * 2 ^ b : Nat) : ℝ) := by
  simp only [familyFrequency,
    accumulatedPositive_unprocessedSwitchFiber_card
      processed blockAt stage hstage block value,
    accumulatedPositiveNormalForm_card]

theorem accumulatedPositive_unprocessedUniversal_frequency {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (point : Fin 3) :
    familyFrequency (accumulatedPositiveNormalForm processed blockAt)
      (stage, (block, Sum.inr point)) =
        ((2 ^ b : Nat) : ℝ) /
          ((processed.card + (r - processed.card) * 2 ^ b : Nat) : ℝ) := by
  simp only [familyFrequency,
    accumulatedPositive_unprocessedUniversalFiber_card
      processed blockAt stage hstage block point,
    accumulatedPositiveNormalForm_card]

theorem accumulatedPositive_processed_frequency {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed) :
    familyFrequency (accumulatedPositiveNormalForm processed blockAt)
      (stage, (blockAt stage, Sum.inr 0)) =
        (1 : ℝ) /
          ((processed.card + (r - processed.card) * 2 ^ b : Nat) : ℝ) := by
  simp only [familyFrequency,
    accumulatedPositive_processedFiber_card processed blockAt stage hstage,
    accumulatedPositiveNormalForm_card]
  norm_num

theorem filteredAccumulated_unprocessed_frequency {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (vertex : ProductVertex b) :
    familyFrequency
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex) =
        (((4 * b) ^ (r - processed.card - 1) : Nat) : ℝ) /
          (((4 * b) ^ (r - processed.card) : Nat) : ℝ) := by
  simp only [familyFrequency,
    filteredAccumulated_unprocessedFiber_card
      processed blockAt choiceAt stage hstage vertex,
    filterWithin_accumulatedStagedRegion_card]

theorem filteredAccumulated_processed_frequency {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed)
    (hpositive : 0 < b) :
    familyFrequency
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, (blockAt stage, Sum.inr 0)) = 1 := by
  simp only [familyFrequency,
    filteredAccumulated_processedFiber_card
      processed blockAt choiceAt stage hstage,
    filterWithin_accumulatedStagedRegion_card]
  have hne : (((4 * b) ^ (r - processed.card) : Nat) : ℝ) ≠ 0 := by
    positivity
  exact div_self hne

theorem processed_card_lt_of_stage_not_mem {r : Nat}
    (processed : Finset (Fin r)) (stage : Fin r)
    (hstage : stage ∉ processed) : processed.card < r := by
  have hne : processed ≠ (Finset.univ : Finset (Fin r)) := by
    intro heq
    apply hstage
    rw [heq]
    exact Finset.mem_univ stage
  have hproper : processed ⊂ (Finset.univ : Finset (Fin r)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ processed, hne⟩
  simpa using Finset.card_lt_card hproper

theorem accumulatedPositive_switch_frequency_ge {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (value : Bool) (hpositive : 0 < b) :
    (1 : ℝ) / (2 * r) ≤
      familyFrequency (accumulatedPositiveNormalForm processed blockAt)
        (stage, (block, Sum.inl value)) := by
  rw [accumulatedPositive_unprocessedSwitch_frequency
    processed blockAt stage hstage block value]
  have hcard : processed.card ≤ r :=
    (processed_card_lt_of_stage_not_mem processed stage hstage).le
  have hcardLt : processed.card < r :=
    processed_card_lt_of_stage_not_mem processed stage hstage
  have hpowPositive : 0 < 2 ^ b := pow_pos (by omega : 0 < (2 : Nat)) b
  have hself : processed.card ≤ processed.card * 2 ^ b := by
    calc
      processed.card = processed.card * 1 := by omega
      _ ≤ processed.card * 2 ^ b :=
        Nat.mul_le_mul_left processed.card (Nat.one_le_iff_ne_zero.mpr
          (ne_of_gt hpowPositive))
  have hden :
      processed.card + (r - processed.card) * 2 ^ b ≤ r * 2 ^ b := by
    calc
      processed.card + (r - processed.card) * 2 ^ b ≤
          processed.card * 2 ^ b + (r - processed.card) * 2 ^ b :=
        Nat.add_le_add_right hself _
      _ = (processed.card + (r - processed.card)) * 2 ^ b := by ring
      _ = r * 2 ^ b := by rw [Nat.add_sub_of_le hcard]
  have hpow : 2 ^ b = 2 * 2 ^ (b - 1) := by
    conv_lhs => rw [show b = (b - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hcrossNat :
      processed.card + (r - processed.card) * 2 ^ b ≤
        2 ^ (b - 1) * (2 * r) := by
    exact hden.trans_eq (by rw [hpow]; ring)
  have hrNat : 0 < 2 * r := by
    have := processed_card_lt_of_stage_not_mem processed stage hstage
    omega
  have hdenPositiveNat :
      0 < processed.card + (r - processed.card) * 2 ^ b := by
    have hremaining : 0 < r - processed.card := Nat.sub_pos_of_lt hcardLt
    have hproduct : 0 < (r - processed.card) * 2 ^ b :=
      Nat.mul_pos hremaining hpowPositive
    exact Nat.lt_of_lt_of_le hproduct (Nat.le_add_left _ processed.card)
  have hrReal : (0 : ℝ) < 2 * r := by exact_mod_cast hrNat
  have hdenReal : (0 : ℝ) <
      (processed.card + (r - processed.card) * 2 ^ b : Nat) := by
    exact_mod_cast hdenPositiveNat
  have hcrossReal :
      (1 : ℝ) * (processed.card + (r - processed.card) * 2 ^ b : Nat) ≤
        (2 ^ (b - 1) : Nat) * (2 * r) := by
    exact_mod_cast (by simpa only [one_mul] using hcrossNat)
  exact (div_le_div_iff₀ hrReal hdenReal).mpr hcrossReal

theorem accumulatedPositive_universal_frequency_ge {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (point : Fin 3) (hpositive : 0 < b) :
    (1 : ℝ) / (2 * r) ≤
      familyFrequency (accumulatedPositiveNormalForm processed blockAt)
        (stage, (block, Sum.inr point)) := by
  rw [accumulatedPositive_unprocessedUniversal_frequency
    processed blockAt stage hstage block point]
  have hswitch := accumulatedPositive_switch_frequency_ge
    processed blockAt stage hstage block false hpositive
  rw [accumulatedPositive_unprocessedSwitch_frequency
    processed blockAt stage hstage block false] at hswitch
  exact hswitch.trans (div_le_div_of_nonneg_right (by
    norm_num
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ (2 : Nat))
      (Nat.sub_le b 1)) (by positivity))

theorem filteredAccumulated_unprocessed_frequency_eq {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (vertex : ProductVertex b)
    (hpositive : 0 < b) :
    familyFrequency
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt))
      (stage, vertex) = (1 : ℝ) / (4 * b) := by
  rw [filteredAccumulated_unprocessed_frequency
    processed blockAt choiceAt stage hstage vertex]
  have hm : 0 < r - processed.card := by
    have := processed_card_lt_of_stage_not_mem processed stage hstage
    omega
  have hpow : (4 * b) ^ (r - processed.card) =
      (4 * b) ^ (r - processed.card - 1) * (4 * b) := by
    conv_lhs => rw [show r - processed.card =
      (r - processed.card - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow]
  push_cast
  have hbase : (0 : ℝ) < 4 * b := by positivity
  have hp : (0 : ℝ) < (4 * b) ^ (r - processed.card - 1) := by positivity
  field_simp

theorem accumulatedPositive_processed_frequency_lt {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed)
    (hpositive : 0 < b)
    (hsize : 4 * b < processed.card + (r - processed.card) * 2 ^ b) :
    familyFrequency (accumulatedPositiveNormalForm processed blockAt)
      (stage, (blockAt stage, Sum.inr 0)) < (1 : ℝ) / (4 * b) := by
  rw [accumulatedPositive_processed_frequency
    processed blockAt stage hstage]
  have hpositiveBase : (0 : ℝ) < 4 * b := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < (4 : Nat)) hpositive
  have hcast : (4 * b : ℝ) <
      (processed.card + (r - processed.card) * 2 ^ b : Nat) := by
    exact_mod_cast hsize
  exact one_div_lt_one_div_of_lt hpositiveBase hcast

/-- The exact frequency sandwich needed by the staged hybrid branch rule.
Every vertex of an unprocessed component is frequent on the positive side and
infrequent on the negative side, while every already processed distinguished
vertex has the opposite profile. -/
theorem accumulated_frequency_sandwich {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (ω : ℝ)
    (hpositive : 0 < b)
    (hsize : 4 * b < processed.card + (r - processed.card) * 2 ^ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    (∀ stage ∉ processed, ∀ block value,
      ω ≤ familyFrequency (accumulatedPositiveNormalForm processed blockAt)
        (stage, (block, Sum.inl value))) ∧
    (∀ stage ∉ processed, ∀ block point,
      ω ≤ familyFrequency (accumulatedPositiveNormalForm processed blockAt)
        (stage, (block, Sum.inr point))) ∧
    (∀ stage ∉ processed, ∀ vertex,
      familyFrequency
        (filterWithin (blocker (stagedProductFamily r b))
          (accumulatedStagedRegion processed blockAt choiceAt))
        (stage, vertex) < ω) ∧
    (∀ stage ∈ processed,
      familyFrequency (accumulatedPositiveNormalForm processed blockAt)
        (stage, (blockAt stage, Sum.inr 0)) < ω) ∧
    (∀ stage ∈ processed,
      familyFrequency
        (filterWithin (blocker (stagedProductFamily r b))
          (accumulatedStagedRegion processed blockAt choiceAt))
        (stage, (blockAt stage, Sum.inr 0)) = 1) := by
  constructor
  · intro stage hstage block value
    exact hupper.trans (accumulatedPositive_switch_frequency_ge
      processed blockAt stage hstage block value hpositive)
  constructor
  · intro stage hstage block point
    exact hupper.trans (accumulatedPositive_universal_frequency_ge
      processed blockAt stage hstage block point hpositive)
  constructor
  · intro stage hstage vertex
    rw [filteredAccumulated_unprocessed_frequency_eq
      processed blockAt choiceAt stage hstage vertex hpositive]
    exact hlower
  constructor
  · intro stage hstage
    exact (accumulatedPositive_processed_frequency_lt
      processed blockAt stage hstage hpositive hsize).trans hlower
  · intro stage hstage
    exact filteredAccumulated_processed_frequency
      processed blockAt choiceAt stage hstage hpositive

/-- A member eligible for the positive strong-cover branch: none of its
vertices is positive-infrequent. -/
def IsPositiveBranchCandidate {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (ω : ℝ) (E : Finset α) : Prop :=
  E ∈ F ∧ ∀ x ∈ E, ω ≤ familyFrequency F x

theorem unprocessedStage_isPositiveBranchCandidate {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (E : Finset (ProductVertex b)) (hE : E ∈ switchProductFamily b)
    (ω : ℝ) (hpositive : 0 < b)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    IsPositiveBranchCandidate (accumulatedPositiveNormalForm processed blockAt)
      ω (stageLift stage E) := by
  classical
  constructor
  · apply Finset.mem_union_right
    exact (mem_stagedProductFamilyOutside_iff processed _).mpr
      ⟨stage, hstage, E, hE, rfl⟩
  · rintro ⟨other, vertex⟩ hvertex
    have hparts := (mem_stageLift stage E other vertex).mp hvertex
    have hother : other = stage := hparts.1
    subst other
    rcases vertex with ⟨block, side⟩
    cases side with
    | inl value =>
        exact hupper.trans (accumulatedPositive_switch_frequency_ge
          processed blockAt stage hstage block value hpositive)
    | inr point =>
        exact hupper.trans (accumulatedPositive_universal_frequency_ge
          processed blockAt stage hstage block point hpositive)

theorem accumulatedPositive_processedOtherFiber_eq_empty {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed) (vertex : ProductVertex b)
    (hne : vertex ≠ (blockAt stage, Sum.inr 0)) :
    familyVertexFiber (accumulatedPositiveNormalForm processed blockAt)
      (stage, vertex) = ∅ := by
  classical
  ext A
  constructor
  · intro hA
    obtain ⟨hNormal, hvertex⟩ := Finset.mem_filter.mp hA
    rcases Finset.mem_union.mp hNormal with hProcessed | hOutside
    · obtain ⟨other, hother, hEq⟩ :=
        (mem_processedSingletonFamily_iff processed blockAt A).mp hProcessed
      have hmember :
          (stage, vertex) ∈
            ({(other, (blockAt other, Sum.inr 0))} :
              Finset (StagedProductVertex r b)) := hEq ▸ hvertex
      have hpairs := Finset.mem_singleton.mp hmember
      have hstageEq : stage = other := congrArg Prod.fst hpairs
      subst other
      exact False.elim (hne (congrArg Prod.snd hpairs))
    · obtain ⟨other, hother, E, hE, hEq⟩ :=
        (mem_stagedProductFamilyOutside_iff processed A).mp hOutside
      have hLift : (stage, vertex) ∈ stageLift other E := hEq ▸ hvertex
      have hstageEq : stage = other :=
        (mem_stageLift other E stage vertex).mp hLift |>.1
      subst other
      exact (hother hstage).elim
  · intro hA
    simp at hA

theorem accumulatedPositive_processed_frequency_lt_all {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∈ processed) (vertex : ProductVertex b)
    (ω : ℝ) (hpositive : 0 < b)
    (hsize : 4 * b < processed.card + (r - processed.card) * 2 ^ b)
    (hlower : (1 : ℝ) / (4 * b) < ω) :
    familyFrequency (accumulatedPositiveNormalForm processed blockAt)
      (stage, vertex) < ω := by
  by_cases hvertex : vertex = (blockAt stage, Sum.inr 0)
  · subst vertex
    exact (accumulatedPositive_processed_frequency_lt
      processed blockAt stage hstage hpositive hsize).trans hlower
  · rw [familyFrequency,
      accumulatedPositive_processedOtherFiber_eq_empty
        processed blockAt stage hstage vertex hvertex]
    simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    have hbase : (0 : ℝ) < (1 : ℝ) / (4 * b) := by positivity
    exact hbase.trans hlower

/-- The pivot case of the hybrid recursion asks for a vertex frequent in both
families. -/
def HasFrequentPivot {α : Type*} [DecidableEq α]
    (F G : Finset (Finset α)) (ω : ℝ) : Prop :=
  ∃ x, ω ≤ familyFrequency F x ∧ ω ≤ familyFrequency G x

theorem accumulated_hasNoFrequentPivot {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (ω : ℝ)
    (hpositive : 0 < b)
    (hsize : 4 * b < processed.card + (r - processed.card) * 2 ^ b)
    (hlower : (1 : ℝ) / (4 * b) < ω) :
    ¬ HasFrequentPivot (accumulatedPositiveNormalForm processed blockAt)
      (filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion processed blockAt choiceAt)) ω := by
  rintro ⟨⟨stage, vertex⟩, hpos, hneg⟩
  by_cases hstage : stage ∈ processed
  · exact (not_lt_of_ge hpos)
      (accumulatedPositive_processed_frequency_lt_all
        processed blockAt stage hstage vertex ω hpositive hsize hlower)
  · exact (not_lt_of_ge hneg) (by
      rw [filteredAccumulated_unprocessed_frequency_eq
        processed blockAt choiceAt stage hstage vertex hpositive]
      exact hlower)

theorem isPositiveBranchCandidate_iff_unprocessedStage {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (ω : ℝ) (hpositive : 0 < b)
    (hsize : 4 * b < processed.card + (r - processed.card) * 2 ^ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r))
    (A : Finset (StagedProductVertex r b)) :
    IsPositiveBranchCandidate (accumulatedPositiveNormalForm processed blockAt)
        ω A ↔
      ∃ stage : Fin r, stage ∉ processed ∧
        ∃ E ∈ switchProductFamily b, stageLift stage E = A := by
  classical
  constructor
  · rintro ⟨hA, hfrequent⟩
    rcases Finset.mem_union.mp hA with hProcessed | hOutside
    · obtain ⟨stage, hstage, hEq⟩ :=
        (mem_processedSingletonFamily_iff processed blockAt A).mp hProcessed
      have hpoint : (stage, (blockAt stage, Sum.inr 0)) ∈ A := by
        rw [← hEq]
        simp
      have hge := hfrequent _ hpoint
      have hlt := accumulatedPositive_processed_frequency_lt_all
        processed blockAt stage hstage (blockAt stage, Sum.inr 0)
        ω hpositive hsize hlower
      exact (not_lt_of_ge hge hlt).elim
    · exact (mem_stagedProductFamilyOutside_iff processed A).mp hOutside
  · rintro ⟨stage, hstage, E, hE, rfl⟩
    exact unprocessedStage_isPositiveBranchCandidate
      processed blockAt stage hstage E hE ω hpositive hupper

theorem stagedCoverRegion_mem_accumulatedStrongCover {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (stage : Fin r) (hstage : stage ∉ processed)
    (block : Fin b) (choice : Fin b → Bool) :
    stagedCoverRegion stage block choice ∈
      strongMemberFullCover (accumulatedPositiveNormalForm processed blockAt)
        (selectedStagedEdge stage) := by
  classical
  simp only [strongMemberFullCover, Finset.mem_biUnion, Finset.mem_image]
  refine ⟨stageLift stage (switchProductEdge choice), ?_,
    (stage, (block, Sum.inr 0)), ?_, rfl⟩
  · apply Finset.mem_union_right
    exact (mem_stagedProductFamilyOutside_iff processed _).mpr
      ⟨stage, hstage, switchProductEdge choice,
        switchProductEdge_mem_family choice, rfl⟩
  · simp [selectedStagedEdge, selectedProductEdge]

/-- Intersecting the current universe with one generated canonical stage
region is exactly the accumulated universe with that stage newly processed. -/
theorem accumulatedStagedRegion_insert {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (block : Fin b)
    (choice : Fin b → Bool) :
    accumulatedStagedRegion processed blockAt choiceAt ∩
        stagedCoverRegion stage block choice =
      accumulatedStagedRegion (insert stage processed)
        (Function.update blockAt stage block)
        (Function.update choiceAt stage choice) := by
  classical
  ext vertex
  simp only [Finset.mem_inter, mem_accumulatedStagedRegion_iff,
    Finset.mem_insert]
  constructor
  · rintro ⟨hold, hnew⟩ current (hEq | hcurrent)
    · subst current
      simpa using hnew
    · have hne : current ≠ stage := by
        intro heq
        subst current
        exact hstage hcurrent
      simpa [Function.update, hne] using hold current hcurrent
  · intro hall
    constructor
    · intro current hcurrent
      have hne : current ≠ stage := by
        intro heq
        subst current
        exact hstage hcurrent
      simpa [Function.update, hne] using hall current (Or.inr hcurrent)
    · simpa using hall stage (Or.inl rfl)

theorem exists_minimalMember_subset {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) {A : Finset α} (hA : A ∈ F) :
    ∃ B ∈ minimalMembers F, B ⊆ A := by
  classical
  let candidates := F.filter fun B => B ⊆ A
  have hnonempty : candidates.Nonempty := by
    exact ⟨A, by simp [candidates, hA]⟩
  obtain ⟨B, hBcandidate, hBmin⟩ :=
    candidates.exists_min_image Finset.card hnonempty
  have hBF : B ∈ F := (Finset.mem_filter.mp hBcandidate).1
  have hBA : B ⊆ A := (Finset.mem_filter.mp hBcandidate).2
  refine ⟨B, Finset.mem_filter.mpr ⟨hBF, ?_⟩, hBA⟩
  intro C hCF hCB
  have hCA : C ⊆ A := hCB.trans hBA
  have hCcandidate : C ∈ candidates :=
    Finset.mem_filter.mpr ⟨hCF, hCA⟩
  have hcard : B.card ≤ C.card := hBmin C hCcandidate
  have hEq : C = B := Finset.eq_of_subset_of_card_le hCB hcard
  simp [hEq]

/-- Deleting nonminimal source members before applying an inclusion-monotone
map does not change the minimal image. -/
theorem minimalMembers_image_minimalMembers_eq {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (F : Finset (Finset α)) (f : Finset α → Finset β)
    (hmono : ∀ {A B}, A ⊆ B → f A ⊆ f B) :
    minimalMembers ((minimalMembers F).image f) =
      minimalMembers (F.image f) := by
  classical
  ext D
  constructor
  · intro hD
    obtain ⟨hDimageMin, hDminimal⟩ := Finset.mem_filter.mp hD
    obtain ⟨A, hAmin, hAD⟩ := Finset.mem_image.mp hDimageMin
    have hAF : A ∈ F := (Finset.mem_filter.mp hAmin).1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨A, hAF, hAD⟩
    · intro C hCimage hCD
      obtain ⟨A', hA'F, hA'C⟩ := Finset.mem_image.mp hCimage
      obtain ⟨B, hBmin, hBA'⟩ := exists_minimalMember_subset F hA'F
      have hfB : f B ∈ (minimalMembers F).image f :=
        Finset.mem_image.mpr ⟨B, hBmin, rfl⟩
      have hfBC : f B ⊆ C := by
        rw [← hA'C]
        exact hmono hBA'
      have hDB : D ⊆ f B := hDminimal (f B) hfB (hfBC.trans hCD)
      exact hDB.trans hfBC
  · intro hD
    obtain ⟨hDimage, hDminimal⟩ := Finset.mem_filter.mp hD
    obtain ⟨A, hAF, hAD⟩ := Finset.mem_image.mp hDimage
    obtain ⟨B, hBmin, hBA⟩ := exists_minimalMember_subset F hAF
    have hBF : B ∈ F := (Finset.mem_filter.mp hBmin).1
    have hfBimage : f B ∈ F.image f := Finset.mem_image.mpr ⟨B, hBF, rfl⟩
    have hfBD : f B ⊆ D := by
      rw [← hAD]
      exact hmono hBA
    have hDB : D ⊆ f B := hDminimal (f B) hfBimage hfBD
    have hEq : f B = D := Finset.Subset.antisymm hfBD hDB
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨B, hBmin, hEq⟩
    · intro C hCimage hCD
      have hCfull : C ∈ F.image f := by
        obtain ⟨A', hA'min, hA'C⟩ := Finset.mem_image.mp hCimage
        exact Finset.mem_image.mpr
          ⟨A', (Finset.mem_filter.mp hA'min).1, hA'C⟩
      exact hDminimal C hCfull hCD

theorem projectWithin_projectWithin {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U V : Finset α) :
    projectWithin (projectWithin F U) V = projectWithin F (U ∩ V) := by
  classical
  rw [projectWithin, projectWithin,
    minimalMembers_image_minimalMembers_eq]
  · unfold projectWithin
    congr 1
    ext D
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨A, ⟨E, hEF, rfl⟩, rfl⟩
      exact ⟨E, hEF, by ext x; simp⟩
    · rintro ⟨E, hEF, rfl⟩
      exact ⟨E ∩ U, ⟨E, hEF, rfl⟩, by ext x; simp⟩
  · intro A B hAB x hx
    exact Finset.mem_inter.mpr
      ⟨hAB (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩

theorem filterWithin_filterWithin {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U V : Finset α) :
    filterWithin (filterWithin F U) V = filterWithin F (U ∩ V) := by
  classical
  ext A
  simp only [filterWithin, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hAF, hAU⟩, hAV⟩
    exact ⟨hAF, fun x hx => Finset.mem_inter.mpr ⟨hAU hx, hAV hx⟩⟩
  · rintro ⟨hAF, hAUV⟩
    exact ⟨⟨hAF, fun x hx => (Finset.mem_inter.mp (hAUV hx)).1⟩,
      fun x hx => (Finset.mem_inter.mp (hAUV hx)).2⟩

theorem projectAccumulatedPositive_into_stageRegion {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (block : Fin b)
    (choice : Fin b → Bool) :
    projectWithin (accumulatedPositiveNormalForm processed blockAt)
        (accumulatedStagedRegion processed blockAt choiceAt ∩
          stagedCoverRegion stage block choice) =
      accumulatedPositiveNormalForm (insert stage processed)
        (Function.update blockAt stage block) := by
  rw [← projectWithin_accumulatedStagedRegion_eq
    processed blockAt choiceAt, projectWithin_projectWithin]
  have hcollapse :
      accumulatedStagedRegion processed blockAt choiceAt ∩
          (accumulatedStagedRegion processed blockAt choiceAt ∩
            stagedCoverRegion stage block choice) =
        accumulatedStagedRegion processed blockAt choiceAt ∩
          stagedCoverRegion stage block choice := by
    ext vertex
    simp
  rw [hcollapse, accumulatedStagedRegion_insert processed blockAt choiceAt
    stage hstage block choice,
    projectWithin_accumulatedStagedRegion_eq]

theorem filterAccumulatedNegative_into_stageRegion {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (block : Fin b)
    (choice : Fin b → Bool) :
    filterWithin
        (filterWithin (blocker (stagedProductFamily r b))
          (accumulatedStagedRegion processed blockAt choiceAt))
        (accumulatedStagedRegion processed blockAt choiceAt ∩
          stagedCoverRegion stage block choice) =
      filterWithin (blocker (stagedProductFamily r b))
        (accumulatedStagedRegion (insert stage processed)
          (Function.update blockAt stage block)
          (Function.update choiceAt stage choice)) := by
  rw [filterWithin_filterWithin]
  have hcollapse :
      accumulatedStagedRegion processed blockAt choiceAt ∩
          (accumulatedStagedRegion processed blockAt choiceAt ∩
            stagedCoverRegion stage block choice) =
        accumulatedStagedRegion processed blockAt choiceAt ∩
          stagedCoverRegion stage block choice := by
    ext vertex
    simp
  rw [hcollapse, accumulatedStagedRegion_insert processed blockAt choiceAt
    stage hstage block choice]

/-- The actual algorithm intersects every abstract strong-cover region with
its current universe. -/
noncomputable def strongMemberFullCoverWithin {α : Type*} [Fintype α]
    [DecidableEq α] [LinearOrder α] (U : Finset α)
    (F : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  (strongMemberFullCover F T).image fun region => U ∩ region

theorem accumulatedStagedCoverRegion_injective {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) :
    Function.Injective (fun code : Fin b × (Fin b → Bool) =>
      accumulatedStagedRegion processed blockAt choiceAt ∩
        stagedCoverRegion stage code.1 code.2) := by
  classical
  have hAllStage : ∀ x : ProductVertex b,
      (stage, x) ∈ accumulatedStagedRegion processed blockAt choiceAt := by
    intro x
    apply (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt (stage, x)).mpr
    intro current hcurrent
    exact untouched_mem_stagedCoverRegion current stage (by
      intro hEq
      subst current
      exact hstage hcurrent) (blockAt current) (choiceAt current) x
  rintro ⟨block, choice⟩ ⟨otherBlock, otherChoice⟩ hRegions
  have hBlockMem := Finset.ext_iff.mp hRegions
    (stage, (block, Sum.inr 0))
  have hBlock : block = otherBlock := by
    simpa [hAllStage] using hBlockMem
  subst otherBlock
  have hChoice : choice = otherChoice := by
    funext index
    have hSwitch := Finset.ext_iff.mp hRegions
      (stage, (index, Sum.inl true))
    simp only [Finset.mem_inter, hAllStage, true_and,
      trueSwitch_mem_stagedCoverRegion_iff] at hSwitch
    cases hLeft : choice index <;> cases hRight : otherChoice index <;>
      simp [hLeft, hRight] at hSwitch ⊢
  exact Prod.ext rfl hChoice

theorem accumulatedStrongCoverWithin_card_ge {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) :
    b * 2 ^ b ≤
      (strongMemberFullCoverWithin
        (accumulatedStagedRegion processed blockAt choiceAt)
        (accumulatedPositiveNormalForm processed blockAt)
        (selectedStagedEdge stage)).card := by
  classical
  let codes : Finset (Fin b × (Fin b → Bool)) := Finset.univ
  let regions := codes.image fun code =>
    accumulatedStagedRegion processed blockAt choiceAt ∩
      stagedCoverRegion stage code.1 code.2
  have hRegions : regions ⊆
      strongMemberFullCoverWithin
        (accumulatedStagedRegion processed blockAt choiceAt)
        (accumulatedPositiveNormalForm processed blockAt)
        (selectedStagedEdge stage) := by
    intro region hRegion
    obtain ⟨code, _, rfl⟩ := Finset.mem_image.mp hRegion
    exact Finset.mem_image.mpr ⟨stagedCoverRegion stage code.1 code.2,
      stagedCoverRegion_mem_accumulatedStrongCover
        processed blockAt stage hstage code.1 code.2, rfl⟩
  calc
    b * 2 ^ b = codes.card := by simp [codes]
    _ = regions.card := by
      exact (Finset.card_image_iff.mpr fun left _ right _ h =>
        accumulatedStagedCoverRegion_injective
          processed blockAt choiceAt stage hstage h).symm
    _ ≤ _ := Finset.card_le_card hRegions

theorem universal_mem_accumulatedStagedRegion_iff_of_mem {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) (index : Fin b) (point : Fin 3) :
    (stage, (index, Sum.inr point)) ∈
        accumulatedStagedRegion processed blockAt choiceAt ↔
      index = blockAt stage ∧ point = 0 := by
  constructor
  · intro hvertex
    have hlocal := (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt _).mp hvertex stage hstage
    simpa using hlocal
  · rintro ⟨hindex, hpoint⟩
    apply (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt _).mpr
    intro current hcurrent
    by_cases hEq : current = stage
    · subst current
      simp [hindex, hpoint]
    · exact untouched_mem_stagedCoverRegion current stage (fun h => hEq h.symm)
        (blockAt current) (choiceAt current) (index, Sum.inr point)

theorem trueSwitch_mem_accumulatedStagedRegion_iff_of_mem {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∈ processed) (index : Fin b) :
    (stage, (index, Sum.inl true)) ∈
        accumulatedStagedRegion processed blockAt choiceAt ↔
      choiceAt stage index = false := by
  constructor
  · intro hvertex
    have hlocal := (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt _).mp hvertex stage hstage
    simpa using hlocal
  · intro hchoice
    apply (mem_accumulatedStagedRegion_iff
      processed blockAt choiceAt _).mpr
    intro current hcurrent
    by_cases hEq : current = stage
    · subst current
      simpa using hchoice
    · exact untouched_mem_stagedCoverRegion current stage (fun h => hEq h.symm)
        (blockAt current) (choiceAt current) (index, Sum.inl true)

noncomputable def finalAccumulatedRegion {r b : Nat}
    (codeAt : Fin r → Fin b × (Fin b → Bool)) :
    Finset (StagedProductVertex r b) :=
  accumulatedStagedRegion Finset.univ
    (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)

theorem finalAccumulatedRegion_injective {r b : Nat} :
    Function.Injective (finalAccumulatedRegion (r := r) (b := b)) := by
  classical
  intro left right hRegions
  funext stage
  apply Prod.ext
  · have hleft :
        (stage, ((left stage).1, Sum.inr 0)) ∈ finalAccumulatedRegion left := by
      exact (universal_mem_accumulatedStagedRegion_iff_of_mem
        Finset.univ (fun stage => (left stage).1)
          (fun stage => (left stage).2) stage (Finset.mem_univ stage)
          (left stage).1 0).mpr ⟨rfl, rfl⟩
    have hright :
        (stage, ((left stage).1, Sum.inr 0)) ∈ finalAccumulatedRegion right := by
      rw [← hRegions]
      exact hleft
    exact (universal_mem_accumulatedStagedRegion_iff_of_mem
      Finset.univ (fun stage => (right stage).1)
        (fun stage => (right stage).2) stage (Finset.mem_univ stage)
        (left stage).1 0).mp hright |>.1
  · funext index
    have hmem : (left stage).2 index = false ↔
        (right stage).2 index = false := by
      constructor
      · intro hleft
        have hleftMem : (stage, (index, Sum.inl true)) ∈
            finalAccumulatedRegion left :=
          (trueSwitch_mem_accumulatedStagedRegion_iff_of_mem
          Finset.univ (fun stage => (left stage).1)
            (fun stage => (left stage).2) stage (Finset.mem_univ stage) index).mpr
          hleft
        have hrightMem : (stage, (index, Sum.inl true)) ∈
            finalAccumulatedRegion right :=
          (Finset.ext_iff.mp hRegions _).mp hleftMem
        exact (trueSwitch_mem_accumulatedStagedRegion_iff_of_mem
          Finset.univ (fun stage => (right stage).1)
            (fun stage => (right stage).2) stage (Finset.mem_univ stage) index).mp
          hrightMem
      · intro hright
        have hrightMem : (stage, (index, Sum.inl true)) ∈
            finalAccumulatedRegion right :=
          (trueSwitch_mem_accumulatedStagedRegion_iff_of_mem
          Finset.univ (fun stage => (right stage).1)
            (fun stage => (right stage).2) stage (Finset.mem_univ stage) index).mpr
          hright
        have hleftMem : (stage, (index, Sum.inl true)) ∈
            finalAccumulatedRegion left :=
          (Finset.ext_iff.mp hRegions _).mpr hrightMem
        exact (trueSwitch_mem_accumulatedStagedRegion_iff_of_mem
          Finset.univ (fun stage => (left stage).1)
            (fun stage => (left stage).2) stage (Finset.mem_univ stage) index).mp
          hleftMem
    cases hLeft : (left stage).2 index <;>
      cases hRight : (right stage).2 index <;>
      simp [hLeft, hRight] at hmem ⊢

noncomputable def finalAccumulatedRegions (r b : Nat) :
    Finset (Finset (StagedProductVertex r b)) :=
  (Finset.univ : Finset (Fin r → Fin b × (Fin b → Bool))).image
    finalAccumulatedRegion

theorem finalAccumulatedRegions_card (r b : Nat) :
    (finalAccumulatedRegions r b).card = (b * 2 ^ b) ^ r := by
  classical
  rw [finalAccumulatedRegions,
    Finset.card_image_iff.mpr fun left _ right _ h =>
      finalAccumulatedRegion_injective h]
  simp

end IrrRAFEnumeration

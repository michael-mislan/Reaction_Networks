import proofs.RAFInteriorRealizability.Main

namespace RAFInteriorRealizability

open RAF RAF.Frankl

universe u


variable {E : Type u} [Fintype E] [DecidableEq E]

/-- A literal finite source whose only observable is its family of
food-generated reaction subsets. -/
structure FoodGenerationRealization (E : Type u) [Fintype E]
    [DecidableEq E] where
  M : Type u
  fintypeM : Fintype M
  decEqM : DecidableEq M
  Q : @CRS M E decEqM

def FoodGenerationFamilyRealizable
    (F : Finset (Finset E)) : Prop :=
  ∃ W : FoodGenerationRealization E,
    ∀ S : Finset E, @FoodGenerated W.M E W.decEqM W.Q S ↔ S ∈ F

def IsAntimatroidFamily (F : Finset (Finset E)) : Prop :=
  ∃ A : AntimatroidData E, A.family = F

/-- Exact representation theorem for the temporal half of RAF semantics:
finite food-generation families are precisely finite antimatroids. -/
theorem foodGenerationFamilyRealizable_iff_antimatroid
    (F : Finset (Finset E)) :
    FoodGenerationFamilyRealizable F ↔ IsAntimatroidFamily F := by
  constructor
  · rintro ⟨W, hW⟩
    letI : DecidableEq W.M := W.decEqM
    refine ⟨foodGeneratedAntimatroid W.Q, ?_⟩
    change foodGeneratedFamily W.Q = F
    apply Finset.ext
    intro S
    rw [mem_foodGeneratedFamily]
    exact hW S
  · rintro ⟨A, rfl⟩
    refine ⟨{
      M := MarkerMolecule E
      fintypeM := inferInstance
      decEqM := inferInstance
      Q := MarkerSource.crs A
    }, ?_⟩
    exact MarkerSource.foodGenerated_iff_mem A

/-- Every reaction subset is food-generated. This is the food-generation
condition of an elementary CRS, isolated from catalysis. -/
def AllFoodGenerated {M : Type u} [DecidableEq M]
    (Q : CRS M E) : Prop :=
  ∀ S : Finset E, FoodGenerated Q S

/-- In an elementary source, the entire fixed family is exactly the static
predecessor-supported family extracted from food and product catalysts. -/
theorem elementary_fixedFamily_iff_predSupported
    {M : Type u} [DecidableEq M] (Q : CRS M E) (C : Catalysis M E)
    (hElementary : AllFoodGenerated Q) (S : Finset E) :
    S ∈ fixedFamily Q C ↔ PredSupported (extractedPredecessors Q C) S := by
  rw [fixedFamily_iff_foodGenerated_and_predSupported]
  simp only [foodGeneratedAntimatroid]
  rw [mem_foodGeneratedFamily]
  simp [hElementary S]

/-- The canonical two-role paired realization of an arbitrary finite interior
operator: every fixed set is represented by its producer/gate pair set, and
there are no additional fixed sets. -/
theorem pairGadget_fixedFamily_exact (ψ : InteriorOperator E) :
    (∀ S : Finset E,
      S ∈ ψ.family ↔
        PairGadget.encode S ∈
          fixedFamily (PairGadget.crs ψ) PairGadget.catalysis) ∧
    (∀ T : Finset (PairReaction E),
      T ∈ fixedFamily (PairGadget.crs ψ) PairGadget.catalysis →
        ∃ S ∈ ψ.family, T = PairGadget.encode S) := by
  constructor
  · intro S
    rw [mem_fixedFamily]
    by_cases hzero : S = ∅
    · subst S
      simp [ψ.empty_mem, PairGadget.encode]
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
      have hencne : PairGadget.encode S ≠ ∅ := by
        obtain ⟨e, heS⟩ := hne
        intro h
        have : PairReaction.producer e ∈ PairGadget.encode S :=
          (PairGadget.producer_mem_encode S e).2 heS
        rw [h] at this
        simp at this
      rw [PairGadget.encoded_isRAF_iff_mem]
      simp [hencne, hne]
  · intro T hT
    rw [mem_fixedFamily] at hT
    rcases hT with hzero | hraf
    · subst T
      exact ⟨∅, ψ.empty_mem, by simp [PairGadget.encode]⟩
    · have hmem : T ∈ rafFamily (PairGadget.crs ψ) PairGadget.catalysis :=
        (mem_rafFamily _ _ T).2 hraf
      rw [PairGadget.rafFamily_eq_image] at hmem
      rcases Finset.mem_image.mp hmem with ⟨S, hS, rfl⟩
      exact ⟨S, (Finset.mem_erase.mp hS).2, rfl⟩

/-- A concise reaction-fusion invariant. The value one means that the logical
producer and gate roles can be fused on the original ground set; otherwise the
paired construction supplies two roles per coordinate. -/
noncomputable def reactionFusionNumber (ψ : InteriorOperator E) : Nat :=
  by
    classical
    exact if SameGroundRAFRealizable ψ then 1 else 2

theorem reactionFusionNumber_le_two (ψ : InteriorOperator E) :
    reactionFusionNumber ψ ≤ 2 := by
  classical
  by_cases h : SameGroundRAFRealizable ψ
  · simp [reactionFusionNumber, h]
  · simp [reactionFusionNumber, h]

theorem reactionFusionNumber_eq_one_iff (ψ : InteriorOperator E) :
    reactionFusionNumber ψ = 1 ↔ SameGroundRAFRealizable ψ := by
  classical
  simp [reactionFusionNumber]

/-- Two roles always suffice, with exact fixed-family image, while the main
characterization says precisely when those roles fuse to one. -/
theorem reactionFusionDichotomy (ψ : InteriorOperator E) :
    reactionFusionNumber ψ ≤ 2 ∧
      (reactionFusionNumber ψ = 1 ↔ FoodSupportCertificate ψ) ∧
      (∀ S : Finset E,
        S ∈ ψ.family ↔ PairGadget.encode S ∈
          fixedFamily (PairGadget.crs ψ) PairGadget.catalysis) := by
  refine ⟨reactionFusionNumber_le_two ψ, ?_,
    (pairGadget_fixedFamily_exact ψ).1⟩
  rw [reactionFusionNumber_eq_one_iff,
    sameGroundRAFRealizable_iff_foodSupportCertificate]

end RAFInteriorRealizability

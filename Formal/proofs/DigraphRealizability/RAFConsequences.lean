import proofs.DigraphRealizability.TraceChecker
import proofs.RAFInteriorRealizability.Corollaries

namespace DigraphRealizability
open RAF RAF.Frankl RAFInteriorRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable def supportData (P : E → Finset E) : InteriorOperator E := by
  classical
  exact {
    family := Finset.univ.filter (PredSupported P)
    empty_mem := by simp [PredSupported]
    union_mem := by
      intro A B hA hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA hB ⊢
      intro r hr
      rcases Finset.mem_union.mp hr with hr | hr
      · obtain ⟨u, hu, hp⟩ := hA r hr
        exact ⟨u, Finset.mem_union_left _ hu, hp⟩
      · obtain ⟨u, hu, hp⟩ := hB r hr
        exact ⟨u, Finset.mem_union_right _ hu, hp⟩ }

@[simp] theorem mem_supportData (P : E → Finset E) (S : Finset E) :
    S ∈ (supportData P).family ↔ PredSupported P S := by
  classical
  simp [supportData]

theorem reconstructed_interior_eq (F : InteriorOperator E) (P : E → Finset E)
    (h : ∀ S, S ∈ F.family ↔ PredSupported P S) :
    (supportData P).apply = F.apply := by
  apply InteriorOperator.apply_eq_of_family_eq
  ext S
  exact (mem_supportData P S).trans (h S).symm

def elementarySource : CRS (Option E) E :=
  { inputs := fun _ => {none}, outputs := fun r => {some r}, food := {none} }

def elementaryCatalysis (P : E → Finset E) : Catalysis (Option E) E
  | none, _ => False
  | some u, r => u ∈ P r

omit [Fintype E] in
theorem elementary_allFood : AllFoodGenerated (elementarySource : CRS (Option E) E) := by
  intro S r _
  exact ⟨0, Finset.Subset.refl _⟩

theorem elementary_predecessors (P : E → Finset E) :
    extractedPredecessors elementarySource (elementaryCatalysis P) = P := by
  classical
  funext r
  ext u
  simp [extractedPredecessors, elementarySource, elementaryCatalysis]

def elementaryRealization (P : E → Finset E) : LiteralRealization E :=
  { M := Option E, fintypeM := inferInstance, decEqM := inferInstance,
    Q := elementarySource, C := elementaryCatalysis P }

theorem elementary_fixed_exact (P : E → Finset E) (S : Finset E) :
    S ∈ (elementaryRealization P).fixedData.family ↔ PredSupported P S := by
  change S ∈ fixedFamily elementarySource (elementaryCatalysis P) ↔ _
  rw [elementary_fixedFamily_iff_predSupported _ _ elementary_allFood,
    elementary_predecessors]

def IsElementary (W : LiteralRealization E) : Prop := by
  letI : DecidableEq W.M := W.decEqM
  exact AllFoodGenerated W.Q

def ElementaryFamilyRealizable (F : Finset (Finset E)) : Prop :=
  ∃ W : LiteralRealization E, IsElementary W ∧ W.fixedData.family = F

theorem elementary_iff_peeling (F : Finset (Finset E)) :
    ElementaryFamilyRealizable F ↔ IntrinsicPeelable F := by
  rw [← digraphRealizable_iff_intrinsicPeeling]
  constructor
  · rintro ⟨W, hw, he⟩
    letI := W.decEqM
    refine ⟨extractedPredecessors W.Q W.C, ?_⟩
    intro S
    rw [← he]
    exact elementary_fixedFamily_iff_predSupported W.Q W.C hw S
  · rintro ⟨P,hP⟩
    refine ⟨elementaryRealization P, elementary_allFood (E := E), ?_⟩
    ext S
    exact (elementary_fixed_exact P S).trans (hP S).symm

theorem raf_iff_antimatroid_peeling (F : InteriorOperator E) :
    SameGroundRAFRealizable F ↔
      ∃ A : AntimatroidData E, ∃ H : Finset (Finset E),
        IntrinsicPeelable H ∧ F.family = A.family ∩ H := by
  rw [rafInteriorOperator_realizable_iff]
  constructor
  · rintro ⟨A,P,h⟩
    refine ⟨A,(supportData P).family, ?_, ?_⟩
    · exact (digraphRealizable_iff_intrinsicPeeling _).mp ⟨P,mem_supportData P⟩
    · ext S
      simpa using h S
  · rintro ⟨A,H,hH,heq⟩
    obtain ⟨P,hP⟩ := (digraphRealizable_iff_intrinsicPeeling H).mpr hH
    refine ⟨A,P,?_⟩
    intro S
    rw [heq, Finset.mem_inter, hP]
end DigraphRealizability

import proofs.DigraphRealizability.HornElimination
import Mathlib.Data.Finset.Sort
namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Lightweight graph semantics; definitionally equal to the existing RAF predicate.
The source bridge is exported in PublicationResolution. -/
def VertexSupported (P : E → Finset E) (S : Finset E) : Prop :=
  ∀ r ∈ S, ∃ u ∈ S, u ∈ P r

def eliminateVertex (P : E → Finset E) (v r : E) : Finset E :=
  if r = v then ∅ else if v ∈ P r then
    if v ∈ P v then {r} else (P r).erase v ∪ P v
  else P r

omit [Fintype E] in
theorem eliminate_forward (P : E → Finset E) (v : E) {S : Finset E}
    (h : VertexSupported P S) : VertexSupported (eliminateVertex P v) (S.erase v) := by
  intro r hr
  obtain ⟨hrv,hrS⟩ := Finset.mem_erase.mp hr
  obtain ⟨u,huS,huP⟩ := h r hrS
  by_cases hv : v ∈ P r
  · by_cases hloop : v ∈ P v
    · exact ⟨r,hr,by simp [eliminateVertex,hrv,hv,hloop]⟩
    · by_cases huv : u = v
      · subst u
        obtain ⟨w,hwS,hwP⟩ := h v huS
        have hwv : w ≠ v := by intro he; subst w; exact hloop hwP
        exact ⟨w,Finset.mem_erase.mpr ⟨hwv,hwS⟩,
          by simp [eliminateVertex,hrv,hv,hloop,hwP]⟩
      · exact ⟨u,Finset.mem_erase.mpr ⟨huv,huS⟩,
          by simp [eliminateVertex,hrv,hv,hloop,huv,huP]⟩
  · have huv : u ≠ v := by intro he; subst u; exact hv huP
    exact ⟨u,Finset.mem_erase.mpr ⟨huv,huS⟩,
      by simpa [eliminateVertex,hrv,hv] using huP⟩

omit [Fintype E] in
theorem eliminate_lift (P : E → Finset E) (v : E) {T : Finset E}
    (h : VertexSupported (eliminateVertex P v) T) :
    ∃ S, VertexSupported P S ∧ S.erase v = T := by
  classical
  have hvT : v ∉ T := by
    intro hv
    obtain ⟨u,_,hu⟩ := h v hv
    simp [eliminateVertex] at hu
  by_cases hloop : v ∈ P v
  · refine ⟨insert v T, ?_, by simp [hvT]⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact ⟨r,Finset.mem_insert_self _ _,hloop⟩
    · by_cases hv : v ∈ P r
      · exact ⟨v,Finset.mem_insert_self _ _,hv⟩
      · obtain ⟨u,hu,huP⟩ := h r hr
        have hrv : r ≠ v := by intro he; subst r; exact hvT hr
        exact ⟨u,Finset.mem_insert_of_mem hu, by simpa [eliminateVertex,hrv,hv] using huP⟩
  · by_cases hex : ∃ u ∈ T, u ∈ P v
    · refine ⟨insert v T, ?_, by simp [hvT]⟩
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · obtain ⟨u,hu,hp⟩ := hex
        exact ⟨u,Finset.mem_insert_of_mem hu,hp⟩
      · by_cases hv : v ∈ P r
        · exact ⟨v,Finset.mem_insert_self _ _,hv⟩
        · obtain ⟨u,hu,huP⟩ := h r hr
          have hrv : r ≠ v := by intro he; subst r; exact hvT hr
          exact ⟨u,Finset.mem_insert_of_mem hu,by simpa [eliminateVertex,hrv,hv] using huP⟩
    · refine ⟨T,?_,Finset.erase_eq_of_notMem hvT⟩
      intro r hr
      obtain ⟨u,hu,huP⟩ := h r hr
      have hrv : r ≠ v := by intro he; subst r; exact hvT hr
      by_cases hv : v ∈ P r
      · simp only [eliminateVertex,if_neg hrv,if_pos hv,if_neg hloop,
          Finset.mem_union,Finset.mem_erase] at huP
        rcases huP with huP | huP
        · exact ⟨u,hu,huP.2⟩
        · exact False.elim (hex ⟨u,hu,huP⟩)
      · exact ⟨u,hu,by simpa [eliminateVertex,hrv,hv] using huP⟩

omit [Fintype E] in
theorem single_vertex_projection (P : E → Finset E) (v : E) (T : Finset E) :
    VertexSupported (eliminateVertex P v) T ↔
      ∃ S, VertexSupported P S ∧ S.erase v = T := by
  constructor
  · exact eliminate_lift P v
  · rintro ⟨S,hS,rfl⟩
    exact eliminate_forward P v hS

omit [Fintype E] in
theorem arbitrary_projection (P : E → Finset E) (H : Finset E) :
    ∃ Q : E → Finset E, ∀ T,
      VertexSupported Q T ↔ ∃ S, VertexSupported P S ∧ S \ H = T := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨P,by intro T; simp⟩
  | @insert v H _ ih =>
    obtain ⟨Q,hQ⟩ := ih
    refine ⟨eliminateVertex Q v,?_⟩
    intro T
    rw [single_vertex_projection]
    constructor
    · rintro ⟨U,hU,he⟩
      obtain ⟨S,hS,rfl⟩ := (hQ U).mp hU
      refine ⟨S,hS,?_⟩
      have eq : S \ insert v H = (S \ H).erase v := by ext x; simp; tauto
      exact eq.trans he
    · rintro ⟨S,hS,rfl⟩
      refine ⟨S \ H,(hQ _).mpr ⟨S,hS,rfl⟩,?_⟩
      ext x
      simp
      tauto
def visibleSet {V : Finset E} (T : Finset {r // r ∈ V}) : Finset E :=
  T.image Subtype.val

def visibleRows (Q : E → Finset E) (V : Finset E) (r : {r // r ∈ V}) :
    Finset {r // r ∈ V} := (Q r.val).subtype (fun x => x ∈ V)

omit [Fintype E] in
theorem visible_support (Q : E → Finset E) (V : Finset E)
    (T : Finset {r // r ∈ V}) :
    VertexSupported (visibleRows Q V) T ↔ VertexSupported Q (visibleSet T) := by
  constructor
  · intro h a ha
    change a ∈ T.image Subtype.val at ha
    obtain ⟨r,hrT,hra⟩ := Finset.mem_image.mp ha
    subst a
    obtain ⟨u,hu,hp⟩ := h r hrT
    exact ⟨u.val,Finset.mem_image.mpr ⟨u,hu,rfl⟩,by simpa [visibleRows] using hp⟩
  · intro h r hr
    obtain ⟨a,ha,hp⟩ := h r.val (Finset.mem_image.mpr ⟨r,hr,rfl⟩)
    change a ∈ T.image Subtype.val at ha
    obtain ⟨u,huT,hua⟩ := Finset.mem_image.mp ha
    subst a
    exact ⟨u,huT,by simpa [visibleRows] using hp⟩

theorem projection_on_visible (P : E → Finset E) (V : Finset E) :
    ∃ Q : {r // r ∈ V} → Finset {r // r ∈ V}, ∀ T,
      VertexSupported Q T ↔ ∃ S, VertexSupported P S ∧ S ∩ V = visibleSet T := by
  classical
  obtain ⟨Q,hQ⟩ := arbitrary_projection P Vᶜ
  refine ⟨visibleRows Q V,?_⟩
  intro T
  rw [visible_support,hQ]
  simp

theorem hidden_vertices_cannot_rescue (V : Finset E)
    (F : Finset (Finset {r // r ∈ V}))
    (hn : ¬ ∃ Q, ∀ T, T ∈ F ↔ VertexSupported Q T) :
    ¬ ∃ P : E → Finset E, ∀ T,
      T ∈ F ↔ ∃ S, VertexSupported P S ∧ S ∩ V = visibleSet T := by
  rintro ⟨P,hP⟩
  obtain ⟨Q,hQ⟩ := projection_on_visible P V
  exact hn ⟨Q,fun T => (hP T).trans (hQ T).symm⟩

noncomputable def familyInterior (F : Finset (Finset E)) (X : Finset E) : Finset E := by
  classical
  exact (F.filter fun S => S ⊆ X).biUnion id

omit [Fintype E] in
@[simp] theorem mem_familyInterior (F : Finset (Finset E)) (X : Finset E) (r : E) :
    r ∈ familyInterior F X ↔ ∃ S ∈ F, S ⊆ X ∧ r ∈ S := by
  classical
  simp [familyInterior,and_assoc]

def projectFamily (F : Finset (Finset E)) (V : Finset E) : Finset (Finset E) :=
  F.image fun S => S ∩ V

theorem projected_interior (F : Finset (Finset E)) (V X : Finset E) :
    familyInterior (projectFamily F V) X = familyInterior F (X ∪ Vᶜ) ∩ V := by
  classical
  ext r
  simp only [mem_familyInterior,Finset.mem_inter]
  constructor
  · rintro ⟨T,hT,hTX,hrT⟩
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    refine ⟨⟨S,hS,?_,(Finset.mem_inter.mp hrT).1⟩,(Finset.mem_inter.mp hrT).2⟩
    intro u hu
    by_cases hv : u ∈ V
    · exact Finset.mem_union_left _ (hTX (Finset.mem_inter.mpr ⟨hu,hv⟩))
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hv)
  · rintro ⟨⟨S,hS,hSX,hrS⟩,hrV⟩
    refine ⟨S ∩ V,Finset.mem_image.mpr ⟨S,hS,rfl⟩,?_,Finset.mem_inter.mpr ⟨hrS,hrV⟩⟩
    intro u hu
    obtain ⟨huS,huV⟩ := Finset.mem_inter.mp hu
    rcases Finset.mem_union.mp (hSX huS) with hx | hc
    · exact hx
    · exact False.elim (Finset.mem_compl.mp hc huV)
end DigraphRealizability

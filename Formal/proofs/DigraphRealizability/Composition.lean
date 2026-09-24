import proofs.DigraphRealizability.RAFConsequences
import proofs.DigraphRealizability.TraceConsequences
namespace DigraphRealizability
open RAF RAF.Frankl RAFInteriorRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

def restrictRows (P : E → Finset E) (V : Finset E) (r : E) :=
  if r ∈ V then P r ∩ V else ∅

omit [Fintype E] in
theorem induced_deletion (P : E → Finset E) (V S : Finset E) :
    PredSupported (restrictRows P V) S ↔ S ⊆ V ∧ PredSupported P S := by
  constructor
  · intro h
    constructor
    · intro r hr
      obtain ⟨u,_,hu⟩ := h r hr
      by_contra hn
      simp [restrictRows,hn] at hu
    · intro r hr
      obtain ⟨u,hu, hp⟩ := h r hr
      by_cases hv : r ∈ V
      · exact ⟨u,hu,(Finset.mem_inter.mp (by simpa [restrictRows,hv] using hp)).1⟩
      · simp [restrictRows,hv] at hp
  · rintro ⟨hV,hP⟩ r hr
    obtain ⟨u,hu,hp⟩ := hP r hr
    exact ⟨u,hu,by simp [restrictRows,hV hr,hp,hV hu]⟩

def sumRows {J : Type*} (P : E → Finset E) (Q : J → Finset J) :
    E ⊕ J → Finset (E ⊕ J)
  | .inl r => (P r).map Function.Embedding.inl
  | .inr r => (Q r).map Function.Embedding.inr

omit [Fintype E] [DecidableEq E] in
theorem independent_product {J : Type*} [DecidableEq J]
    (P : E → Finset E) (Q : J → Finset J) (S : Finset E) (T : Finset J) :
    PredSupported (sumRows P Q) (S.disjSum T) ↔ PredSupported P S ∧ PredSupported Q T := by
  simp [PredSupported, sumRows, Sum.forall, Sum.exists]

def conjunctionFamily : Finset (Finset (Fin 3)) := {∅,{0},{1},{0,1},{0,1,2}}

def conjunctionLeft (r : Fin 3) : Finset (Fin 3) := if r = 1 then {1} else {0}
def conjunctionRight (r : Fin 3) : Finset (Fin 3) := if r = 0 then {0} else {1}

theorem conjunction_intersection : ∀ S,
    PredSupported conjunctionLeft S ∧ PredSupported conjunctionRight S ↔
      S ∈ conjunctionFamily := by
  unfold PredSupported conjunctionLeft conjunctionRight conjunctionFamily
  decide

theorem conjunction_not_realizable :
    ¬ ∃ P : Fin 3 → Finset (Fin 3), ∀ S, S ∈ conjunctionFamily ↔ PredSupported P S := by
  rintro ⟨P,h⟩
  have h0 : 0 ∈ P 0 := (singleton_support P 0).mp ((h {0}).mp (by decide))
  have h1 : 1 ∈ P 1 := (singleton_support P 1).mp ((h {1}).mp (by decide))
  have hn : 2 ∉ P 2 := by
    intro hp
    have hh := (h {2}).mpr ((singleton_support P 2).mpr hp)
    exact (by decide : {2} ∉ conjunctionFamily) hh
  obtain ⟨u,_,hp⟩ := (h {0,1,2}).mp (by decide) 2 (by decide)
  fin_cases u
  · have hs : PredSupported P {0,2} := by
      intro r hr
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨0,by simp,h0⟩
      · exact ⟨0,by simp,hp⟩
    have hh := (h {0,2}).mpr hs
    exact (by decide : {0,2} ∉ conjunctionFamily) hh
  · have hs : PredSupported P {1,2} := by
      intro r hr
      simp only [Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact ⟨1,by simp,h1⟩
      · exact ⟨1,by simp,hp⟩
    have hh := (h {1,2}).mpr hs
    exact (by decide : {1,2} ∉ conjunctionFamily) hh
  · exact hn hp

def conjunctionAntimatroid : AntimatroidData (Fin 3) :=
  { family := conjunctionFamily
    empty_mem := by decide
    union_mem := by decide
    accessible := by decide }

theorem conjunction_general_realizable :
    SameGroundRAFRealizable conjunctionAntimatroid.toUnionClosedData := by
  apply (rafInteriorOperator_realizable_iff _).mpr
  refine ⟨conjunctionAntimatroid,fun r => {r},?_⟩
  intro S
  have hs : PredSupported (fun r : Fin 3 => {r}) S := by
    intro r hr
    exact ⟨r,hr,by simp⟩
  simp [hs]
end DigraphRealizability

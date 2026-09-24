import proofs.DigraphRealizability.Composition
import proofs.DigraphRealizability.Projection
import proofs.DigraphRealizability.ResidualPolicy
import proofs.DigraphRealizability.Obstructions

namespace DigraphRealizability
variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem vertexSupported_iff_predSupported (P : E → Finset E) (S : Finset E) :
    VertexSupported P S ↔ RAFInteriorRealizability.PredSupported P S := Iff.rfl

theorem source_projection_on_visible (P : E → Finset E) (V : Finset E) :
    ∃ Q : {r // r ∈ V} → Finset {r // r ∈ V}, ∀ T,
      RAFInteriorRealizability.PredSupported Q T ↔ ∃ S,
        RAFInteriorRealizability.PredSupported P S ∧ S ∩ V = visibleSet T := by
  simpa only [vertexSupported_iff_predSupported] using projection_on_visible P V

theorem publication_resolution (F : Finset (Finset E)) :
    (∃ P : E → Finset E, ∀ S, S ∈ F ↔ RAFInteriorRealizability.PredSupported P S) ↔
      IntrinsicPeelable F := digraphRealizable_iff_intrinsicPeeling F

end DigraphRealizability

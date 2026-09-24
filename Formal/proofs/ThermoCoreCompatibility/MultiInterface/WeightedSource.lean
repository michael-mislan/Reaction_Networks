import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair
import proofs.ThermoCoreCompatibility.Hypergraph.GradedSource

namespace ThermoCoreCompatibility.MultiInterface

open Hypergraph

namespace WeightedSource

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
    (G : PairAssembly V E) (w : E → Factors)

def network : ReversibleCRN V (E × Bool) where
  reactant := G.network.reactant
  product := G.network.product
  barrier := fun r => if r.2 then (w r.1).b else (w r.1).a
  barrier_pos := by
    rintro ⟨e,b⟩
    cases b
    · exact (w e).a_pos
    · exact (w e).b_pos

def motif (e : E) : Motif (network G w) := (G.motif e).rebase (network G w)

theorem isPAC (e : E) : (motif G w e).IsPAC :=
  Motif.rebase_isPAC (G.motif e) rfl rfl (G.source_isPAC e)

theorem current_productive_iff [Fintype V] (e : E) (z : V → ℝ) :
    (motif G w e).Productive ((network G w).current z) ↔
      (w e).Productive (z (G.src e)) (z (G.dst e)) := by
  rw [motif, Motif.rebase_productive_iff (Q' := network G w)
    (G.motif e) ((network G w).current z) rfl rfl, G.productive_iff]
  simp only [ReversibleCRN.current, network, PairAssembly.network, activity_atom,
    pow_one, Bool.false_eq_true, ↓reduceIte, Factors.Productive]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

end WeightedSource
end ThermoCoreCompatibility.MultiInterface

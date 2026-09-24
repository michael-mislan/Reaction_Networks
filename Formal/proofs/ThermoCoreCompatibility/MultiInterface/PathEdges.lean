import proofs.ThermoCoreCompatibility.MultiInterface.PathCoordinates

namespace ThermoCoreCompatibility.MultiInterface.Path

def Edge : Path → Type
  | .single _ => Unit
  | .snoc p _ => Sum p.Edge Unit

def edgeSource : (p : Path) → p.Edge → p.Vertex
  | .single _, _ => false
  | .snoc p _, .inl e => .inl (p.edgeSource e)
  | .snoc p _, .inr _ => .inl p.last

def edgeTarget : (p : Path) → p.Edge → p.Vertex
  | .single _, _ => true
  | .snoc p _, .inl e => .inl (p.edgeTarget e)
  | .snoc _ _, .inr _ => .inr ()

def edgeFactors : (p : Path) → p.Edge → Factors
  | .single w, _ => w
  | .snoc p _, .inl e => p.edgeFactors e
  | .snoc _ w, .inr _ => w

theorem productiveState_iff_edges (p : Path) (z : p.Vertex → ℝ) :
    p.ProductiveState z ↔ ∀ e, (p.edgeFactors e).Productive
      (z (p.edgeSource e)) (z (p.edgeTarget e)) := by
  induction p with
  | single w => simp [ProductiveState,edgeFactors,edgeSource,edgeTarget,Edge]
  | snoc p w ih =>
    change (p.ProductiveState (fun v => z (.inl v)) ∧
      w.Productive (z (.inl p.last)) (z (.inr ()))) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hp,hw⟩ e
      cases e with
      | inl e => exact hp e
      | inr _ => exact hw
    · intro h
      exact ⟨fun e => h (.inl e),h (.inr ())⟩

end ThermoCoreCompatibility.MultiInterface.Path

import proofs.ThermoCoreCompatibility.BeyondJunction.OrderClosure
import proofs.ThermoCoreCompatibility.MultiInterface.WeightedSource

namespace ThermoCoreCompatibility.BeyondJunction

open MultiInterface Hypergraph

theorem boxed_source_iff {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V]
    (A : PairAssembly V E) (w : E → Factors) (lo hi z : V → ℝ) :
    ((∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
      ∀ e, (WeightedSource.motif A w e).Productive
        ((WeightedSource.network A w).current z)) ↔
      BoxedProductive A.src A.dst w lo hi z := by
  unfold BoxedProductive
  simp only [WeightedSource.current_productive_iff]

theorem normalized_margin_productions (w : Factors) (x y eps : ℝ)
    (hl : eps ≤ y-w.lower x) (hu : eps ≤ w.upper x-y) :
    (w.a+2*w.b)*eps ≤ 2*(w.b*(y-x^2))-w.a*(x-y) ∧
    (w.a+w.b)*eps ≤ w.a*(x-y)-w.b*(y-x^2) := by
  rw [w.residual_lower, w.residual_upper]
  exact ⟨mul_le_mul_of_nonneg_left hl w.lower_den_pos.le,
    mul_le_mul_of_nonneg_left hu w.upper_den_pos.le⟩

end ThermoCoreCompatibility.BeyondJunction

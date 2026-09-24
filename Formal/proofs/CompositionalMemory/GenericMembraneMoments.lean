import proofs.CompositionalMemory.GenericBoundedJumpMoments
import proofs.CompositionalMemory.MembraneMoments

namespace CompositionalMemory

/-- Uniform shared-growth energy moments from bilinear bounds on its literal
concentration jumps. The consuming channel is included exactly once. -/
theorem generic_membrane_energy_moments {V : Type*}
    [AddCommGroup V] [Module ℝ V] {k : ℕ} (hk : 1 ≤ k) (i : Fin k)
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hQ : ∀ x y, Q x y=Q y x)
    (y : V) (jump : Fin k → V) (z : Fin k → ℝ) (γ m N U Z L r : ℝ)
    (hγ : 0 ≤ γ) (hN : 0 < N) (hm : (k : ℝ)*N ≤ m)
    (hU : 0 ≤ U) (hZ : 0 ≤ Z) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hz0 : ∀ j, 0 ≤ z j) (hz : ∀ j, z j ≤ Z)
    (hu : ∀ j, |Q y (jump j)| ≤ L*r*((U+if j=i then (k : ℝ) else 0)/(m+1)))
    (hv : ∀ j, |Q (jump j) (jump j)| ≤ L*((U+if j=i then (k : ℝ) else 0)/(m+1))^2) :
    (∑ j, (γ*(m/k)*z j)*(Q (y+jump j) (y+jump j)-Q y y)) ≤
      2*L*r*(γ*Z*(U+1))+L*(γ*Z*(U+1)^2/N) ∧
    (∑ j, (γ*(m/k)*z j)*(Q (y+jump j) (y+jump j)-Q y y)^2) ≤
      8*L^2*r^2*γ*Z*(U+1)^2/N+2*L^2*γ*Z*(U+1)^4/N^3 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hm0 : 0 < m := lt_of_lt_of_le (mul_pos hk0 hN) hm
  have h := bounded_bilinear_jump_moments Q hQ y jump
    (fun j => γ*(m/k)*z j) (fun j => (U+if j=i then (k : ℝ) else 0)/(m+1))
    L r ((U+1)/N) (γ*Z*(U+1)) (γ*Z*(U+1)^2/N) hL hr
    (fun j => mul_nonneg (mul_nonneg hγ (div_nonneg hm0.le hk0.le)) (hz0 j))
    (fun j => by dsimp only; split_ifs <;> positivity)
    (fun j => membrane_jump_size hk i j m N U hN hm hU) hu hv
    (membrane_first_moment hk i z γ m U Z hγ hm0 hU hZ hz)
    (membrane_moment_uniform hk i z γ m N U Z hγ hN hm hU hZ hz)
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  field_simp

end CompositionalMemory

import proofs.RAF1519.Refinement.MarkMoments
import proofs.RAF1519.Refinement.CountPhaseBinding

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 200000

theorem local_mark_square_bound (m : PhysicalMark) (d V : ℝ) (N : Fin 7 → ℕ)
    (hV : 0 < V) (hd : d ≤ 1/25)
    (hA : materialA (concentration V N) ≤ 11/10)
    (hB : materialB (concentration V N) ≤ 11/10) :
    localMarkedMoment m 1 d V N ≤ (9/4)*V := by
  have ha : (N 0:ℝ)+N 2+2*N 3+2*N 4+2*N 5+N 6 ≤ (11/10)*V := by
    have he : ((N 0:ℝ)+N 2+2*N 3+2*N 4+2*N 5+N 6)/V =
        materialA (concentration V N) := by
      change _ = (N 0:ℝ)/V+N 2/V+2*(N 3/V)+2*(N 4/V)+2*(N 5/V)+N 6/V
      ring
    exact (div_le_iff₀ hV).mp (he.trans_le hA)
  have hb : (N 1:ℝ)+N 2+N 3+2*N 4+2*N 5+N 6 ≤ (11/10)*V := by
    have he : ((N 1:ℝ)+N 2+N 3+2*N 4+2*N 5+N 6)/V =
        materialB (concentration V N) := by
      change _ = (N 1:ℝ)/V+N 2/V+N 3/V+2*(N 4/V)+2*(N 5/V)+N 6/V
      ring
    exact (div_le_iff₀ hV).mp (he.trans_le hB)
  have hdX := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (N 2) : (0:ℝ) ≤ N 2)
  have hdD := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (N 6) : (0:ℝ) ≤ N 6)
  have hN : ∀ s, (0:ℝ) ≤ N s := fun s => Nat.cast_nonneg _
  cases m <;> norm_num [localMarkedMoment] <;>
    nlinarith [hN 0,hN 1,hN 2,hN 3,hN 4,hN 5,hN 6]

/-- Before material exit all five actual marked counters have square-jump
    intensity at most9/(4V). No favorable post-noise intermediate bound is used. -/
theorem marked_variance_bound {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : 0 < V) (hd : ∀ i, d i ≤ 1/25) (N : MolecularState n)
    (hsafe : materialSafe V N) (i : Fin n) (m : PhysicalMark) :
    (∑ a, molecularRate r d k V N a*(markIncrement V i m N a)^2) ≤ 9/(4*V) := by
  rw [graph_normalized_mark_moment r d k V hV.ne' N i m 1]
  have hmat := materialSafe_material_upper V N hsafe i
  have hb := local_mark_square_bound m (d i) V (fun s => N (i,s)) hV (hd i) hmat.1 hmat.2
  apply (div_le_iff₀ (sq_pos_of_pos hV)).mpr
  calc
    _ ≤ (9/4)*V := hb
    _ = (9/(4*V))*V^2 := by field_simp

end
end RAF1519.Refinement

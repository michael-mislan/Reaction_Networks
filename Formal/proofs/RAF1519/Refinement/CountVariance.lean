import proofs.RAF1519.Refinement.CountRateBounds
import proofs.RAF1519.Refinement.CountJumps

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

theorem molecular_increment_square {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : 0 < V)
    (p : Fin n × Fin 7) (N : MolecularState n) (a : CountChannel n) :
    (molecularIncrement r d k V p N a)^2 ≤ (2/V)^2 := by
  have h := molecular_increment_bound r d k V hV p N a
  have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ 2/V by positivity)).mpr h
  simpa only [sq_abs] using hs

theorem local_coordinate_variance {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V)
    (p : Fin n × Fin 7) (N : MolecularState n) (hN : ∀ q, (N q:ℝ)/V ≤ 11/10) :
    (∑ a : Fin n × LocalChannel, molecularRate r d k V N (.inl a)*
      (molecularIncrement r d k V p N (.inl a))^2) ≤ 800/V := by
  have hnode (i : Fin n) :
      (∑ a : LocalChannel, molecularRate r d k V N (.inl (i,a))*
        (molecularIncrement r d k V p N (.inl (i,a)))^2) ≤
        if i=p.1 then 800/V else 0 := by
    by_cases hi : i=p.1
    · rw [if_pos hi]
      have hs : (∑ a : LocalChannel, molecularRate r d k V N (.inl (i,a))) ≤ 200*V := by
        change (∑ a : LocalChannel, (atNode i (localReaction (r i) (d i) a)).rate V N) ≤ _
        simp_rw [atNode_rate]
        exact local_total_rate_bound (r i) (d i) V (hr i) (hd i) hV _ (fun s => hN (i,s))
      calc
        _ ≤ ∑ a : LocalChannel, molecularRate r d k V N (.inl (i,a))*(2/V)^2 := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (molecular_increment_square r d k V hV p N _)
            (molecular_rate_nonnegative r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV.le N _)
        _ = (∑ a : LocalChannel, molecularRate r d k V N (.inl (i,a)))*(2/V)^2 := by
          rw [Finset.sum_mul]
        _ ≤ (200*V)*(2/V)^2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
        _ = 800/V := by field_simp; norm_num
    · rw [if_neg hi]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro a _
      rw [local_increment_off_node r d k V N p i a (Ne.symm hi)]
      simp
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i : Fin n, if i=p.1 then 800/V else 0 := Finset.sum_le_sum (fun i _ => hnode i)
    _ = _ := by simp

end
end RAF1519.Refinement

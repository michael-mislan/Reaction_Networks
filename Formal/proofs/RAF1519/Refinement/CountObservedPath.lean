import proofs.RAF1519.Refinement.CountNoise
import proofs.RAF1519.Refinement.GraphDrift

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

theorem consistent_molecular_increment {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (p : Fin n × Fin 7) (N : MolecularState n)
    (y : JumpState (MolecularState n) (CountChannel n))
    (hy : jumpConsistent (molecularNext r d k) N y) :
    y.2.1.elim (fun _ => 0) (molecularIncrement r d k V p N) =
      ((y.1 p:ℝ)-(N p:ℝ))/V := by
  obtain ⟨a,ha,hN⟩ := hy
  rw [ha,hN]
  rfl

theorem molecular_changes_telescope {n : ℕ} (V : ℝ) (p : Fin n × Fin 7)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) :
    (∑ i : Fin K, (((z ((i:ℕ)+1)).1 p:ℝ)-((z i).1 p:ℝ))/V) =
      (((z K).1 p:ℝ)-((z 0).1 p:ℝ))/V := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Fin.sum_univ_castSucc]
    change (∑ i : Fin K, (((z ((i:ℕ)+1)).1 p:ℝ)-((z i).1 p:ℝ))/V)+
      (((z (K+1)).1 p:ℝ)-((z K).1 p:ℝ))/V = _
    rw [ih]
    ring

/-- Before stopping, the compensated prefix is the observed count change minus
    the literal generator integrated over its completed holding intervals. -/
theorem molecular_complete_prefix_identity {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V T : ℝ) (p : Fin n × Fin 7)
    (good : Set (MolecularState n))
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ)
    (hc : ∀ i < K, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hs : ∀ i < K, ¬coordinateStop good T stop i (Preorder.frestrictLe i z))
    (ht : ∀ i < K, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z)) :
    coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p) good T stop z K =
      (((z K).1 p:ℝ)-((z 0).1 p:ℝ))/V-
      ∑ i : Fin K, (∑ a, molecularRate r d k V (z i).1 a*
        molecularIncrement r d k V p (z i).1 a)*(z ((i:ℕ)+1)).2.2 := by
  unfold coordinatePrefix
  calc
    _ = ∑ i : Fin K, ((((z ((i:ℕ)+1)).1 p:ℝ)-((z i).1 p:ℝ))/V-
        (∑ a, molecularRate r d k V (z i).1 a*
          molecularIncrement r d k V p (z i).1 a)*(z ((i:ℕ)+1)).2.2) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold coordinateCompensation
      dsimp only
      rw [if_neg (hs i i.isLt),if_pos (ht i i.isLt),min_eq_left (ht i i.isLt)]
      simp only [Preorder.frestrictLe_apply]
      rw [consistent_molecular_increment r d k V p _ _ (hc i i.isLt)]
    _ = _ := by rw [Finset.sum_sub_distrib,molecular_changes_telescope]

end
end RAF1519.Refinement

import proofs.RAF1519.Refinement.CountObservedPath
import proofs.RAF1519.Refinement.HoldingPrimitive

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 20000

theorem prefix_elapsed_holdingClock {α β : Type*} (z : ℕ → JumpState α β) (K : ℕ) :
    prefixElapsed K (Preorder.frestrictLe K z) = holdingClock (fun i => (z (i+1)).2.2) K := rfl

def countDriftPrimitive {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (p : Fin n × Fin 7) (t : ℝ) : ℝ :=
  ((z 0).1 p:ℝ)/V+holdingPrimitive (fun i => (z (i+1)).2.2)
    (fun i => ∑ a, molecularRate r d k V (z i).1 a*molecularIncrement r d k V p (z i).1 a) K t

theorem countDriftPrimitive_continuous {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (p : Fin n × Fin 7) :
    Continuous (countDriftPrimitive r d k V z K p) :=
  continuous_const.add (holdingPrimitive_continuous _ _ _)

theorem countDriftPrimitive_right_derivative {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K j : ℕ) (hj : j < K) (p : Fin n × Fin 7) (t : ℝ)
    (ha : prefixElapsed j (Preorder.frestrictLe j z) ≤ t)
    (hb : t < prefixElapsed j (Preorder.frestrictLe j z)+(z (j+1)).2.2) :
    HasDerivWithinAt (countDriftPrimitive r d k V z K p)
      (∑ a, molecularRate r d k V (z j).1 a*molecularIncrement r d k V p (z j).1 a) (Set.Ici t) t := by
  exact (holdingPrimitive_right_derivative _ _ hh K j hj t ha hb).const_add _

/-- Exact identity on an actual holding interval, including its initial jump. -/
theorem count_minus_compensation_primitive {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V T : ℝ) (p : Fin n × Fin 7)
    (good : Set (MolecularState n))
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K j : ℕ) (hj : j < K) (t : ℝ) (hT : t ≤ T)
    (ha : prefixElapsed j (Preorder.frestrictLe j z) ≤ t)
    (hb : t < prefixElapsed j (Preorder.frestrictLe j z)+(z (j+1)).2.2)
    (hc : ∀ i < j, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hs : ∀ i ≤ j, ¬coordinateStop good T stop i (Preorder.frestrictLe i z)) :
    ((z j).1 p:ℝ)/V-coordinateWithin (molecularRate r d k V) (molecularIncrement r d k V p)
      good T stop z j (t-prefixElapsed j (Preorder.frestrictLe j z)) =
      countDriftPrimitive r d k V z K p t := by
  have hbefore : ∀ i < j, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh (Nat.succ_le_of_lt hi)
    rw [holdingClock_succ] at hm
    change prefixElapsed i (Preorder.frestrictLe i z)+(z (i+1)).2.2 ≤
      prefixElapsed j (Preorder.frestrictLe j z) at hm
    linarith
  rw [coordinateWithin,if_neg (hs j le_rfl),
    molecular_complete_prefix_identity r d k V T p good stop z j hc
      (fun i hi => hs i hi.le) hbefore]
  rw [countDriftPrimitive,holdingPrimitive_on_interval _ _ hh K j hj t ha hb]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ a, molecularRate r d k V (z i).1 a*molecularIncrement r d k V p (z i).1 a)*
      (z (i+1)).2.2) j]
  simp only [prefix_elapsed_holdingClock]
  ring

end
end RAF1519.Refinement

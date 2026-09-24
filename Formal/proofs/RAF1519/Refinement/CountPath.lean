import proofs.RAF1519.Refinement.CountEndpoint
import proofs.RAF1519.Refinement.HoldingIndex

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 20000

def countPathIndex {n : ℕ} (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (t : ℝ) : ℕ :=
  holdingIndex (fun i => (z (i+1)).2.2) t

def countPath {n : ℕ} (V : ℝ) (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (t : ℝ) (p : Fin n × Fin 7) : ℝ := ((z (countPathIndex z t)).1 p:ℝ)/V

theorem countPathIndex_spec {n : ℕ}
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) :
    countPathIndex z t < K ∧ prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z) ≤ t ∧
      t < prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z)+
        (z (countPathIndex z t+1)).2.2 :=
  holdingIndex_before_prefix _ hh K t ht hK

theorem countPrimitive_path_derivative {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K : ℕ) (p : Fin n × Fin 7) (t : ℝ) (ht : 0 ≤ t)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) :
    HasDerivWithinAt (countDriftPrimitive r d k V z K p)
      (∑ a, molecularRate r d k V (z (countPathIndex z t)).1 a*
        molecularIncrement r d k V p (z (countPathIndex z t)).1 a) (Set.Ici t) t := by
  have hi := countPathIndex_spec z hh K t ht hK
  exact countDriftPrimitive_right_derivative r d k V z hh K _ hi.1 p t hi.2.1 hi.2.2

/-- Source-specific uniform noise control transferred to the actual time-indexed
    count path, on any interval for which the history stop has not fired. -/
theorem countPath_primitive_noise {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p stop)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z))
    (hs : ∀ i ≤ countPathIndex z t, ¬coordinateStop (countCorridor V) 4 stop i (Preorder.frestrictLe i z))
    (p : Fin n × Fin 7) :
    |countPath V z t p-countDriftPrimitive r d k V z K p t| < countTolerance Δ := by
  let j := countPathIndex z t
  let s := t-prefixElapsed j (Preorder.frestrictLe j z)
  have hi := countPathIndex_spec z hh K t ht hK
  have hs0 : 0 ≤ s := sub_nonneg.mpr hi.2.1
  have hsh : s ≤ min (z (j+1)).2.2 (4-prefixElapsed j (Preorder.frestrictLe j z)) := by
    apply le_min
    · dsimp [s,j]
      linarith [hi.2.2]
    · exact sub_le_sub_right hT _
  have he := count_minus_compensation_primitive r d k V 4 p (countCorridor V) stop z hh
    K j hi.1 t hT hi.2.1 hi.2.2 (fun i _ => hc i) hs
  have hb : |coordinateWithin (molecularRate r d k V) (molecularIncrement r d k V p)
      (countCorridor V) 4 stop z j s| < countTolerance Δ := by
    apply lt_of_not_ge
    intro hcross
    exact hnoise p ⟨j,s,hs0,hsh,hcross⟩
  have heq : countPath V z t p-countDriftPrimitive r d k V z K p t =
      coordinateWithin (molecularRate r d k V) (molecularIncrement r d k V p)
        (countCorridor V) 4 stop z j s := by
    change ((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p t = _
    linarith
  rw [heq]
  exact hb

end
end RAF1519.Refinement

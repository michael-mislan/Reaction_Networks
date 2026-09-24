import proofs.RAF1519.Refinement.MarkNoise
import proofs.RAF1519.Refinement.MarkDrift
import proofs.RAF1519.Refinement.RewardPrimitive
import proofs.RAF1519.Refinement.HoldingIntegral

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

/-- The actual cumulative physical-channel rewards, normalized by V. -/
def markPath {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (t : ℝ) : ℝ :=
  rewardPrefix (markIncrement V i m) z (countPathIndex z t)

def markPrimitive {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (K : ℕ) (t : ℝ) : ℝ :=
  holdingPrimitive (fun j => (z (j+1)).2.2)
    (fun j => ∑ a, molecularRate r d k V (z j).1 a*markIncrement V i m (z j).1 a) K t

theorem mark_primitive_integral {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (i : Fin n) (m : PhysicalMark)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ j, 0 ≤ (z (j+1)).2.2) (K : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hK : b < prefixElapsed K (Preorder.frestrictLe K z)) :
    (∫ t in a..b, markRate m (d i) (fun s => countPath V z t (i,s))) =
      markPrimitive r d k V i m z K b-markPrimitive r d k V i m z K a := by
  have he : (fun t => markRate m (d i) (fun s => countPath V z t (i,s))) =
      fun t => (∑ a, molecularRate r d k V (z (countPathIndex z t)).1 a*
        markIncrement V i m (z (countPathIndex z t)).1 a) := by
    funext t
    exact (physical_mark_drift r d k V hV _ i m).symm
  rw [he]
  exact holdingObservable_integral (fun j => (z (j+1)).2.2)
    (fun j => ∑ a, molecularRate r d k V (z j).1 a*markIncrement V i m (z j).1 a)
    hh K a b ha hab hK

end
end RAF1519.Refinement

import proofs.RAF1519.Refinement.MarkWindows
import proofs.RAF1519.Refinement.HoldingMeasurable

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem countPathIndex_measurable {n : ℕ} (t : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) => countPathIndex z t) := by
  apply (holdingIndex_measurable t).comp
  exact measurable_pi_lambda _ (fun j => (measurable_pi_apply (j+1)).snd.snd)

theorem molecularStateAt_measurable {n : ℕ} (t : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) =>
      (z (countPathIndex z t)).1) := by
  have he : Measurable (fun p : (ℕ → JumpState (MolecularState n) (CountChannel n)) × ℕ =>
      (p.1 p.2).1) := measurable_from_prod_countable_left (fun j => (measurable_pi_apply j).fst)
  exact he.comp (measurable_id.prodMk (countPathIndex_measurable t))

theorem markPrefix_measurable {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark) (K : ℕ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) =>
      rewardPrefix (markIncrement V i m) z K) := by
  unfold rewardPrefix
  apply Finset.measurable_sum
  intro j _
  have he : Measurable (fun a : Unit ⊕ CountChannel n =>
      a.elim (fun _ => (0:ℝ)) (fun a => (physicalMarkReward i m a:ℝ)/V)) :=
    measurable_fun_sum measurable_const (measurable_of_countable _)
  exact he.comp (measurable_pi_apply ((j:ℕ)+1)).snd.fst

theorem markPath_measurable {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark) (t : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) => markPath V i m z t) := by
  have he : Measurable (fun p : (ℕ → JumpState (MolecularState n) (CountChannel n)) × ℕ =>
      rewardPrefix (markIncrement V i m) p.1 p.2) :=
    measurable_from_prod_countable_left (fun K => markPrefix_measurable V i m K)
  exact he.comp (measurable_id.prodMk (countPathIndex_measurable t))

theorem markedWindow_measurable {n : ℕ} (V : ℝ) (i : Fin n) (m : PhysicalMark) (a b : ℝ) :
    Measurable (fun z : ℕ → JumpState (MolecularState n) (CountChannel n) => markedWindow V i m z a b) :=
  (markPath_measurable V i m b).sub (markPath_measurable V i m a)

end
end RAF1519.Refinement

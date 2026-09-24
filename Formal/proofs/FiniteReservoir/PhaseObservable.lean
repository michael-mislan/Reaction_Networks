import proofs.FiniteReservoir.PhaseBounds
import proofs.FiniteCopyReactor.PhaseObservable

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

theorem phase_generator_linear (w : PhaseWeights) (N : Counts) (V r alpha beta : ℝ) :
    generator N V r alpha beta w.obs =
      w.x*coordinateGenerator N V r alpha beta 2+w.c1*coordinateGenerator N V r alpha beta 3+
      w.c2*coordinateGenerator N V r alpha beta 4+w.z*coordinateGenerator N V r alpha beta 5 := by
  unfold coordinateGenerator generator
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [PhaseWeights.obs]
  ring

theorem phase_generator_lower (w : PhaseWeights) (hw : w.Nonneg)
    (N : Counts) (V : ℕ) (r alpha beta : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    phaseDriftLower w N ≤ generator N V r alpha beta w.obs := by
  obtain ⟨h0,h1,h2,h3⟩ := count_phase_comparison N V r alpha beta hV hr hr' hbox hc
  rw [phase_generator_linear]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h0 hw.1) (mul_le_mul_of_nonneg_left h1 hw.2.1))
    (mul_le_mul_of_nonneg_left h2 hw.2.2.1)) (mul_le_mul_of_nonneg_left h3 hw.2.2.2)


end
end FiniteReservoir

import proofs.FiniteCopyReactor.Margins
import proofs.RandomViability.BindingCompetitionDrift

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def concentration (N : Counts) (V : ℝ) : State := fun i => (N i : ℝ)/V
def generator (N : Counts) (V r d : ℝ) (f : Counts → ℝ) : ℝ :=
  ∑ j, CommonPhysicalRealization.physicalRate N V r d 1 1 j *
    (f (CommonPhysicalRealization.physicalNext N j)-f N)

theorem generator_projection (N : Counts) (V r d : ℝ) (f : Counts → ℝ) :
    generator N V r d f = competitionGenerator N V (1/500000000) (1/10) r d f := by
  unfold generator competitionGenerator
  apply Finset.sum_congr rfl
  intro j _
  rw [CommonPhysicalRealization.rate_projection,
    (CommonPhysicalRealization.marked_projection N V r d j).2.1]

theorem material_A_generator (N : Counts) (V r d : ℝ) :
    generator N V r d uCount = V-uCount N := by
  rw [generator_projection, competition_u_drift]

theorem material_B_generator (N : Counts) (V r d : ℝ) :
    generator N V r d wCount = V-wCount N := by
  rw [generator_projection, competition_w_drift]

/-- Exact correction on the literal falling-factorial source, in count units. -/
theorem stock_generator_correction (N : Counts) (V r d : ℝ) (hV : V ≠ 0) :
    generator N V r d weightedCount =
      V*Y (field r d (concentration N V)) + r*(N 2)/(5*V) := by
  rw [generator_projection, competition_growth_expansion, countGrowth_expansion,
    weighted_drift]
  dsimp [concentration]
  field_simp [hV]
  ring

theorem normalized_stock (N : Counts) (V : ℝ) :
    Y (concentration N V) = weightedCount N/V := by
  dsimp [Y, concentration, weightedCount, weighted]
  ring

theorem count_guarded_growth (N : Counts) (V r d : ℝ) (hV : 0 < V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A (concentration N V))
    (hB : 9/10 ≤ B (concentration N V))
    (hY : Y (concentration N V) ≤ 3/50) :
    (2/3)*weightedCount N ≤ generator N V r d weightedCount := by
  have hc : Nonneg (concentration N V) := fun i => div_nonneg (Nat.cast_nonneg _) hV.le
  have h := mul_le_mul_of_nonneg_left
    (interior_guarded_growth r d (concentration N V) hc hr hr' hd hd' hA hB hY) hV.le
  rw [normalized_stock] at h
  have he : V*((2/3)*(weightedCount N/V)) = (2/3)*weightedCount N := by
    field_simp
  rw [he] at h
  rw [stock_generator_correction N V r d (ne_of_gt hV)]
  have hr0 : 0 ≤ r := by linarith
  exact h.trans (le_add_of_nonneg_right (by positivity))

end
end FiniteCopyReactor

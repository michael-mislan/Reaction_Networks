import proofs.FiniteReservoir.PhysicalSource

namespace FiniteReservoir
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open FiniteCopyReactor (reactorTrajectoryFood reactorFood)
open scoped BigOperators

def reactorTrajectory (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) (N : CountState M) :=
  jumpTrajectoryLaw N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)

instance reactorTrajectory_probability (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) (N : CountState M) :
    IsProbabilityMeasure (reactorTrajectory M p V hV N) := by
  unfold reactorTrajectory
  infer_instance

theorem reactor_mass_envelope (M : ℕ) (p : Parameters M) (V : ℝ) (hV : 0 < V) (N : CountState M) :
    ∀ᵐ z ∂reactorTrajectory M p V hV N, ∀ k,
      reactorMass (z k).1 ≤ reactorMass N+∑ i ∈ Finset.range k,reactorTrajectoryFood (z (i+1)).2.1 := by
  have hs := jumpTrajectory_consistent N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
  have hi := jumpTrajectory_initial_population N reactorNext (reactorRate M p V)
    (reactor_rate_nonneg M p V hV) (reactor_total_pos M p V hV)
  filter_upwards [hs,hi] with z hz hinit
  intro k
  induction k with
  | zero => simp [hinit]
  | succ k ih =>
    obtain ⟨j,hj,hn⟩ := hz k
    have hstep := reactor_next_mass M (z k).1 j
    rw [Finset.sum_range_succ,hn,hj]
    change reactorMass (reactorNext (z k).1 j) ≤
      reactorMass N+((∑ i ∈ Finset.range k,reactorTrajectoryFood (z (i+1)).2.1)+reactorFood j)
    omega


end
end FiniteReservoir

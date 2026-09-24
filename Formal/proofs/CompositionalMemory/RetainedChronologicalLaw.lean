import proofs.CompositionalMemory.FrozenRestriction
import proofs.CompositionalMemory.JumpFiniteRestriction
import proofs.CompositionalMemory.CanonicalFiniteLaw

namespace CompositionalMemory
open Classical RandomViability FiniteCopy MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def liftRetainedPayoff {k : ℕ} (D : Finset (ModularCountState k)) (H : StoppedModularState D → ℝ)
    (s : ModularCountState k) : ℝ := if h : s ∈ D then H (some ⟨s,h⟩) else 0

/-- The actual unbounded division-frozen trajectory realizes the canonical retained finite law. -/
theorem retained_chronological_expectation {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (D : Finset (ModularCountState k))
    (hD : ∀ s ∈ D,0 < s.2) (t : NNReal) (H : StoppedModularState D → ℝ)
    (hH0 : H none=0) (hH : ∀ s,0 ≤ H s ∧ H s ≤ 1) (x : {s : ModularCountState k // s ∈ D}) :
    physicalSafeDeadline (frozenCountNext N) (frozenCountRate γ w N)
      (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)
      (D : Set (ModularCountState k)) (fun s => ENNReal.ofReal (liftRetainedPayoff D H s)) x.val t =
      ENNReal.ofReal (finiteTimeExpectation (retainedModularModel γ w hγ hw N D) t H (some x)) := by
  let M := retainedModularModel γ w hγ hw N D
  let F := finiteRestrictionModel (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ hw N) D
  obtain ⟨r,hr,_hr0,hR⟩ := M.exists_clock 0
  obtain ⟨q,hq,hqr,hF⟩ := F.exists_clock r
  have hRq (s) : M.total s ≤ q := (hR s).trans hqr
  have hb (s : ModularCountState k) : ENNReal.ofReal (liftRetainedPayoff D H s) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    unfold liftRetainedPayoff
    split_ifs with hs
    · exact (hH (some ⟨s,hs⟩)).2
    · norm_num
  rw [jump_finite_restriction (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)
    D (fun s => ENNReal.ofReal (liftRetainedPayoff D H s)) hb q hq hF x t]
  rw [frozen_restriction_uniformize γ w hγ hw N D hD q hq hF hRq]
  simp only [causalSafeClock,if_pos t.coe_nonneg]
  have hv : restrictionValue D (fun s => ENNReal.ofReal (liftRetainedPayoff D H s))=
      (fun s => ENNReal.ofReal (H s)) := by
    funext s
    cases s with
    | none => simp [restrictionValue,hH0]
    | some s => simp [restrictionValue,liftRetainedPayoff,s.property]
  rw [hv,safeClockPayoff_univ _ H (fun s => (hH s).1) (fun s => (hH s).2) q t]
  exact congrArg ENNReal.ofReal (finite_time_eq_uniformized M q t hq hRq H (some x)).symm

end
end CompositionalMemory

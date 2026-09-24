import proofs.CoreInteraction.MAF.Forest
import proofs.MAFComposition.Core

/-! Source-level realization of the exact `2 + 2 -> 4` MAF synergy example. -/

namespace CoreInteraction.Examples.MAFCycle

open CoreInteraction

def source : SourceNetwork (Fin 2) (Fin 4) where
  input := ![![1, 0, 1, 0], ![0, 1, 0, 1]]
  output := ![![0, 1, 0, 4], ![4, 0, 1, 0]]
  catalyst := 0

def factorization : Factorization source (Fin 2) Unit where
  owner := ![0, 0, 1, 1]
  support := fun _ _ => True
  support_decidable := fun _ _ => inferInstance
  support_complete := by simp
  coreDecorations := fun _ => ∅

def flux : Fin 4 → ℝ := ![1, 0, 0, 1]

theorem globallyFeasible_four : factorization.GloballyFeasible 4 flux := by
  constructor
  · intro r
    fin_cases r <;> norm_num [flux]
  constructor
  · intro hzero
    have h := congrFun hzero 0
    norm_num [flux] at h
  · intro s
    fin_cases s <;>
      norm_num [Factorization.globalResidual, source, flux, Fin.sum_univ_succ]

theorem no_factor_locallyFeasible_four :
    ∀ f, factorization.FactorActive flux f →
      ¬ factorization.LocallyFeasible 4 flux f := by
  intro f _hactive hlocal
  fin_cases f
  · have h := hlocal.2 0
    norm_num [Factorization.residual, factorization, source, flux,
      Fin.sum_univ_succ] at h
  · have h := hlocal.2 1
    norm_num [Factorization.residual, factorization, source, flux,
      Fin.sum_univ_succ] at h

theorem signed_incidence_cycle_at_four :
    ∃ v, ∃ c : factorization.incidenceGraph.Walk v v, c.IsCycle :=
  factorization.maf_globalFeasible_implies_exists_incidenceCycle 4 flux
    globallyFeasible_four no_factor_locallyFeasible_four

/-- The legacy exact thresholds `2,2,4` and their missing interaction datum are
joined here: the source realization of the `4` witness carries an incidence
cycle extracted from its signed boundary compensation. -/
theorem scalar_two_two_four_maps_to_cycle :
    MAFComposition.ExactThreshold MAFComposition.N1Feasible 2 ∧
    MAFComposition.ExactThreshold MAFComposition.N2Feasible 2 ∧
    MAFComposition.ExactThreshold MAFComposition.N2N1Feasible 4 ∧
    (∃ v, ∃ c : factorization.incidenceGraph.Walk v v, c.IsCycle) :=
  ⟨MAFComposition.n1_exact, MAFComposition.n2_exact,
    MAFComposition.n2n1_exact, signed_incidence_cycle_at_four⟩

end CoreInteraction.Examples.MAFCycle

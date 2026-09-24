import proofs.RAFReactionCriticality.Pivotality
import proofs.RAFReactionCriticality.TargetCuts

namespace RAFReactionCriticality
open scoped BigOperators
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem intervention_gain (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (r : R) (p : ℝ) :
    targetProbability f g r p - targetProbability f f r p =
      p^(orbitSet g r).card * (1-p^(orbitSet f r \ orbitSet g r).card) := by
  have hn := redundant_target_probability f g v h r p
  have ho := redundant_target_probability f f v (fun _ _ => rfl) r p
  change targetProbability f g r p = _ at hn
  change targetProbability f f r p = _ at ho
  rw [hn,ho,Finset.union_self]
  have hc := Finset.card_sdiff_add_card (orbitSet f r) (orbitSet g r)
  rw [← hc,pow_add]
  ring

omit [Fintype R] in
theorem singleton_vulnerability_reduction (E G : Finset R) :
    E.card - (E ∩ G).card = (E \ G).card := by
  have h := Finset.card_sdiff_add_card_inter E G
  omega

theorem total_intervention_gain (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (p : ℝ) :
    expectedSize f g p - expectedSize f f p =
      ∑ r, p^(orbitSet g r).card * (1-p^(orbitSet f r \ orbitSet g r).card) := by
  rw [expectedSize_eq_sum_targets,expectedSize_eq_sum_targets,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => intervention_gain f g v h r p)

end RAFReactionCriticality

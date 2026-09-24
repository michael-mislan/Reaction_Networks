import proofs.PowerLawSmallRAF.BernoulliBitProjection
import proofs.HordijkSteelThreshold.StaticEventContinuity
import proofs.HordijkSteelThreshold.WordEffectiveClosure

namespace PowerLawSmallRAF
open Classical MeasureTheory HordijkSteelThreshold RAF.Polymer unitInterval
open scoped BigOperators
noncomputable section

def staticSubsetEquiv (N : Nat) : (Reaction N → Prop) ≃ Finset (Reaction N) where
  toFun := staticOpenReactions
  invFun H r := r ∈ H
  left_inv ω := by
    classical
    funext r
    apply propext
    simp [staticOpenReactions]
  right_inv H := by
    classical
    ext r
    simp [staticOpenReactions]

theorem staticReactionMeasure_atom_toReal (N : Nat) (a : I) (ω : Reaction N → Prop) :
    (staticReactionMeasure N a {ω}).toReal =
      bernoulliSubsetRowWeight (a : ℝ) (staticOpenReactions ω) := by
  classical
  rw [staticReactionMeasure_atom, ENNReal.coe_toReal]
  rw [← inhomogeneousSubsetWeight_const, inhomogeneousSubsetWeight_eq_prod]
  simp only [NNReal.coe_prod]
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : ω r
  · simp [staticAtomWeight,staticOpenReactions,h]
  · simp [staticAtomWeight,staticOpenReactions,h]

/-- Exact equality of the finite iid measure and the subset-weight event
sum. This does not assert iid independence in the power-law source. -/
theorem staticReactionMeasure_subset_event (N : Nat) (a : I)
    (E : Finset (Reaction N) → Prop) :
    (staticReactionMeasure N a {ω | E (staticOpenReactions ω)}).toReal =
      ∑ H : Finset (Reaction N), if E H then bernoulliSubsetRowWeight (a : ℝ) H else 0 := by
  classical
  let F : Finset (Reaction N → Prop) := Finset.univ.filter (fun ω => E (staticOpenReactions ω))
  have hF : (F : Set (Reaction N → Prop)) = {ω | E (staticOpenReactions ω)} := by
    ext ω
    simp [F]
  rw [← hF, ← sum_measure_singleton, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp only [staticReactionMeasure_atom_toReal]
  change (∑ ω ∈ Finset.univ.filter (fun ω => E (staticOpenReactions ω)),
    bernoulliSubsetRowWeight (a : ℝ) (staticOpenReactions ω)) = _
  rw [Finset.sum_filter]
  apply Fintype.sum_equiv (staticSubsetEquiv N)
  intro ω
  rfl

end
end PowerLawSmallRAF

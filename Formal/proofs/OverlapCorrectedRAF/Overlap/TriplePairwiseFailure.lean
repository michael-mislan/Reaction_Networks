import proofs.OverlapCorrectedRAF.Overlap.ChannelHit

namespace OverlapCorrectedRAF.Overlap

def tripleA : Finset (Fin 4) := {0, 1}
def tripleB : Finset (Fin 4) := {0, 2}
def tripleC₁ : Finset (Fin 4) := {0, 3}
def tripleC₂ : Finset (Fin 4) := {1, 2}

def firstTripleFamily : Finset (Finset (Fin 4)) :=
  {tripleA, tripleB, tripleC₁}

def secondTripleFamily : Finset (Finset (Fin 4)) :=
  {tripleA, tripleB, tripleC₂}

theorem firstTripleFamily_uniform_pair_data :
    (∀ W ∈ firstTripleFamily, W.card = 2) ∧
    (∀ W ∈ firstTripleFamily, ∀ V ∈ firstTripleFamily,
      W ≠ V → (W ∩ V).card = 1) := by
  native_decide

theorem secondTripleFamily_uniform_pair_data :
    (∀ W ∈ secondTripleFamily, W.card = 2) ∧
    (∀ W ∈ secondTripleFamily, ∀ V ∈ secondTripleFamily,
      W ≠ V → (W ∩ V).card = 1) := by
  native_decide

theorem firstTripleFamily_union_card :
    familyUnion firstTripleFamily = {0, 1, 2, 3} := by
  native_decide

theorem secondTripleFamily_union_card :
    familyUnion secondTripleFamily = {0, 1, 2} := by
  native_decide

theorem firstTripleFamily_probability (q : ℝ) :
    localHitProbability q firstTripleFamily =
      1 - 3 * q ^ 2 + 3 * q ^ 3 - q ^ 4 := by
  have hA : tripleA.card = 2 := by native_decide
  have hB : tripleB.card = 2 := by native_decide
  have hC : tripleC₁.card = 2 := by native_decide
  have hAB : (tripleA ∪ tripleB).card = 3 := by native_decide
  have hAC : (tripleA ∪ tripleC₁).card = 3 := by native_decide
  have hBC : (tripleB ∪ tripleC₁).card = 3 := by native_decide
  have hABC : (tripleA ∪ tripleB ∪ tripleC₁).card = 4 := by native_decide
  rw [show firstTripleFamily = {tripleA, tripleB, tripleC₁} by rfl]
  rw [localHitProbability_triple q (by native_decide) (by native_decide)
    (by native_decide)]
  rw [hA, hB, hC, hAB, hAC, hBC, hABC]
  ring

theorem secondTripleFamily_probability (q : ℝ) :
    localHitProbability q secondTripleFamily =
      1 - 3 * q ^ 2 + 2 * q ^ 3 := by
  have hA : tripleA.card = 2 := by native_decide
  have hB : tripleB.card = 2 := by native_decide
  have hC : tripleC₂.card = 2 := by native_decide
  have hAB : (tripleA ∪ tripleB).card = 3 := by native_decide
  have hAC : (tripleA ∪ tripleC₂).card = 3 := by native_decide
  have hBC : (tripleB ∪ tripleC₂).card = 3 := by native_decide
  have hABC : (tripleA ∪ tripleB ∪ tripleC₂).card = 3 := by native_decide
  rw [show secondTripleFamily = {tripleA, tripleB, tripleC₂} by rfl]
  rw [localHitProbability_triple q (by native_decide) (by native_decide)
    (by native_decide)]
  rw [hA, hB, hC, hAB, hAC, hBC, hABC]
  ring

theorem pairwise_data_miss_triple_term (q : ℝ) :
    localHitProbability q firstTripleFamily -
      localHitProbability q secondTripleFamily = q ^ 3 - q ^ 4 := by
  rw [firstTripleFamily_probability, secondTripleFamily_probability]
  ring

end OverlapCorrectedRAF.Overlap

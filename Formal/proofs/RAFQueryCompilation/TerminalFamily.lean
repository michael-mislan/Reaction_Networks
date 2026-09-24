import proofs.RAFQueryCompilation.FamilyArithmeticRun
import proofs.RAFQueryCompilation.IndexedFamilyStructure

namespace RAFQueryCompilation.ModuleFamily
open RAF

/-- Terminal family statement in the declared cached-row/word charge model.
The factor is not a native runtime claim or a lower bound for every algorithm. -/
theorem family_terminal_factor {n : ℕ} (factor : ℕ) (hfactor : 0 < factor)
    (hsize : 1150*factor ≤ n*2+1)
    (A : Finset (Fin (n*2+1))) (edits : List (PairEdit n))
    (hamortized : familySetupCap n < edits.length) :
    (∀ r : Fin (n*2+1), moleculeCode n (some none) ∈
      (indexedSource n).inputs r ∪ (indexedSource n).outputs r) ∧
    (∀ r s : Fin (n*2+1), r ≠ s → ∀ a : ℝ, 0 < a →
      ¬(∀ x, indexedColumn r x = a*indexedColumn s x)) ∧
    ∃ result, familyArithmeticRun A (edits.map encodePairEdit) = some result ∧
      result.members = familyPointTrace edits A ∧
      factor*result.charge < (familyPointBaseline edits
        (compileSource (indexedSource n) (indexedCats n) A).state.available).charge := by
  refine ⟨fun r => indexed_hub_incident r,
    fun r s hne a ha => indexed_no_common_positive_ray hne ha, ?_⟩
  obtain ⟨result,hr,hm,hc⟩ := familyWordRun_correct_bound 8 A edits
  refine ⟨result, by simpa only [familyArithmeticRun_eq] using hr, hm, ?_⟩
  have hsmall : result.charge < 1150*edits.length := by
    norm_num at hc
    omega
  calc
    factor*result.charge < factor*(1150*edits.length) :=
      Nat.mul_lt_mul_of_pos_left hsmall hfactor
    _ = (1150*factor)*edits.length := by ring
    _ ≤ (n*2+1)*edits.length := Nat.mul_le_mul_right edits.length hsize
    _ ≤ _ := familyPointBaseline_reads edits
      (compileSource (indexedSource n) (indexedCats n) A).state.available

end RAFQueryCompilation.ModuleFamily

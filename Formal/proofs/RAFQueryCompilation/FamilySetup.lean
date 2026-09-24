import proofs.RAFQueryCompilation.CompiledSource
import proofs.RAFQueryCompilation.FamilyPointBaseline

namespace RAFQueryCompilation.ModuleFamily
open RAF

def familySetupCap (n : ℕ) : ℕ :=
  let m := n*2+1
  let p := m+1
  m*(14*m+13+2*p) + (m+m*freshRoundCap m 1 1 1 p) +
    (2*m+p+m+m*(m+1)+m*(m+1)+p*(m+1)*(m+1))

theorem family_index_charge (n : ℕ) :
    sourceIndexCharge (indexedSource n) (indexedCats n) =
      (n*2+1)*(14*(n*2+1)+13+2*(n*2+1+1)) := by
  simp [sourceIndexCharge]
  ring

theorem family_setup_bound {n : ℕ} (A : Finset (Fin (n*2+1))) :
    (compileSource (indexedSource n) (indexedCats n) A).charge ≤ familySetupCap n := by
  have ha : A.card ≤ n*2+1 := by simpa using Finset.card_le_univ A
  let answer := (freshEvaluate (indexedSource n) (indexedCats n) A).1
  have hs : answer.card ≤ n*2+1 := by simpa using Finset.card_le_univ answer
  have he := freshEvaluate_bound (indexedSource n) (indexedCats n) A (n*2+1) 1 1 1 ha
    (fun r _ => le_of_eq (indexed_input_card r))
    (fun r _ => le_of_eq (indexed_output_card r))
    (fun r _ => le_of_eq (indexed_catalyst_card r))
  simp only [Fintype.card_fin] at he
  have hr : rebuildCharge (indexedSource n) A answer ≤
      2*(n*2+1)+(n*2+1+1)+(n*2+1)+
        (n*2+1)*(n*2+1+1)+(n*2+1)*(n*2+1+1)+
        (n*2+1+1)*(n*2+1+1)*(n*2+1+1) := by
    simp only [rebuildCharge, indexed_output_card, Finset.sum_const, smul_eq_mul, mul_one]
    gcongr
  change sourceIndexCharge (indexedSource n) (indexedCats n)+
    (freshEvaluate (indexedSource n) (indexedCats n) A).2+
    rebuildCharge (indexedSource n) A answer ≤ _
  rw [family_index_charge]
  exact Nat.add_le_add (Nat.add_le_add_left he _) hr

/-- Startup is the computed compiler charge, rather than a free parameter. -/
theorem family_saves_with_setup {n : ℕ} (A : Finset (Fin (n*2+1)))
    (edits : List (PairEdit n))
    (h : familySetupCap n+1013*edits.length < (n*2+1)*edits.length) :
    (compileSource (indexedSource n) (indexedCats n) A).charge+
      (familyBatch edits (compileSource (indexedSource n) (indexedCats n) A).state).2+
      edits.length <
      (familyPointBaseline edits (compileSource (indexedSource n) (indexedCats n) A).state.available).charge := by
  apply family_saves_against_points
  exact (Nat.add_le_add_right (family_setup_bound A) _).trans_lt h

end RAFQueryCompilation.ModuleFamily

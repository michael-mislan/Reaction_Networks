import proofs.RAF1519.Refinement.CategoricalScale
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι]

def categoricalProbability (c : ι → Fin 3 → ℝ) (E : Set (ι → Fin 3)) : ℝ :=
  ∑ o, if o ∈ E then categoricalMass c o else 0

theorem categoricalProbability_mono (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a)
    {E F : Set (ι → Fin 3)} (h : E ⊆ F) : categoricalProbability c E ≤ categoricalProbability c F := by
  unfold categoricalProbability
  apply Finset.sum_le_sum
  intro o _
  by_cases he : o ∈ E
  · simp only [if_pos he,if_pos (h he),le_refl]
  · simp only [if_neg he]
    split_ifs
    · exact categoricalMass_nonneg c hc o
    · exact le_rfl

theorem categoricalProbability_union (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a)
    (E F : Set (ι → Fin 3)) :
    categoricalProbability c (E ∪ F) ≤ categoricalProbability c E+categoricalProbability c F := by
  unfold categoricalProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro o _
  have hn := categoricalMass_nonneg c hc o
  by_cases he : o ∈ E <;> by_cases hf : o ∈ F <;>
    simp only [Set.mem_union,he,hf,or_self,or_false,false_or,if_true,if_false,zero_add,add_zero,le_refl]
  linarith

theorem categoricalProbability_iUnion {κ : Type*} [Fintype κ]
    (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a) (E : κ → Set (ι → Fin 3)) :
    categoricalProbability c (⋃ k, E k) ≤ ∑ k, categoricalProbability c (E k) := by
  unfold categoricalProbability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro o _
  by_cases ho : o ∈ ⋃ k, E k
  · rw [if_pos ho]
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp ho
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun k => if o ∈ E k then categoricalMass c o else 0)
      (fun k _ => by dsimp only; split_ifs; exact categoricalMass_nonneg c hc o; exact le_rfl) (Finset.mem_univ k)
    simpa only [if_pos hk] using hh
  · rw [if_neg ho]
    exact Finset.sum_nonneg (fun k _ => by split_ifs; exact categoricalMass_nonneg c hc o; exact le_rfl)

end
end RAF1519.Refinement

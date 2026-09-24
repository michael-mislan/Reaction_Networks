import Mathlib.Combinatorics.Colex
import proofs.SmallCusp.Source.Enumeration

namespace SmallCusp

theorem bimol_reaction_index_injective :
    Function.Injective bimolReactionIndex := by
  intro a b h
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  have h₁ : ∀ c : BimolComplexCode, c.index < 6 := by
    intro c
    cases c <;> decide
  have ha₁bound := h₁ a₁
  have ha₂bound := h₁ a₂
  have hb₁bound := h₁ b₁
  have hb₂bound := h₁ b₂
  have h₂ : a₂.index = b₂.index := by
    dsimp [bimolReactionIndex] at h
    omega
  have h₁' : a₁.index = b₁.index := by
    dsimp [bimolReactionIndex] at h
    omega
  have ha₁ : a₁ = b₁ := by
    cases a₁ <;> cases b₁ <;> simp_all [BimolComplexCode.index]
  have ha₂ : a₂ = b₂ := by
    cases a₂ <;> cases b₂ <;> simp_all [BimolComplexCode.index]
  simp [ha₁, ha₂]

theorem bimol_catalogue_key_injective :
    Function.Injective bimolCatalogueKey := by
  intro S T h
  apply Finset.image_injective bimol_reaction_index_injective
  apply Finset.geomSum_injective (n := 2) (by norm_num)
  change (∑ e ∈ S, 2 ^ bimolReactionIndex e) =
    (∑ e ∈ T, 2 ^ bimolReactionIndex e) at h
  have hS :
      (∑ i ∈ S.image bimolReactionIndex, 2 ^ i) =
        ∑ e ∈ S, 2 ^ bimolReactionIndex e := by
    rw [Finset.sum_image]
    exact fun a _ b _ hab => bimol_reaction_index_injective hab
  have hT :
      (∑ i ∈ T.image bimolReactionIndex, 2 ^ i) =
        ∑ e ∈ T, 2 ^ bimolReactionIndex e := by
    rw [Finset.sum_image]
    exact fun a _ b _ hab => bimol_reaction_index_injective hab
  exact hS.trans (h.trans hT.symm)

end SmallCusp

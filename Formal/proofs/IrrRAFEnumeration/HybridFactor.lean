import proofs.IrrRAFEnumeration.AssignmentMinor
import proofs.IrrRAFEnumeration.HybridCharge

namespace IrrRAFEnumeration

variable {α β γ ε δ : Type*}
  [DecidableEq α] [DecidableEq β] [DecidableEq ε] [DecidableEq δ]

/-- A two-level certificate first identifies a reached universe and then a
state inside that universe.  Both levels use a vertex/root-member pair. -/
def twoLevelCharges (U : Finset α) (large : Finset ε) (small : Finset δ) :
    Finset ((α × ε) × (α × δ)) :=
  (U.product large).product (U.product small)

omit [DecidableEq α] [DecidableEq β] [DecidableEq ε] [DecidableEq δ] in
theorem twoLevelCharges_card
    (U : Finset α) (large : Finset ε) (small : Finset δ) :
    (twoLevelCharges U large small).card =
      (U.card * large.card) * (U.card * small.card) := by
  simp [twoLevelCharges]

omit [DecidableEq β] in
/-- Quantitative adapter for the factorized hybrid route.  An injective
universe code and an injective code inside each universe combine into a global
polynomial state code. -/
theorem states_card_le_twoLevelBudget
    (U : Finset α) (large : Finset ε) (small : Finset δ)
    (states : Finset β) (universeOf : β → γ)
    (universeCode : γ → α × ε) (fiberCode : β → α × δ)
    (hUniverseCode :
      ∀ s ∈ states, universeCode (universeOf s) ∈ U.product large)
    (hFiberCode : ∀ s ∈ states, fiberCode s ∈ U.product small)
    (hSeparates :
      ∀ s ∈ states, ∀ t ∈ states,
        universeCode (universeOf s) = universeCode (universeOf t) →
        fiberCode s = fiberCode t → s = t) :
    states.card ≤ (U.card * large.card) * (U.card * small.card) := by
  classical
  let code : β → (α × ε) × (α × δ) := fun s =>
    (universeCode (universeOf s), fiberCode s)
  have hImage : states.image code ⊆ twoLevelCharges U large small := by
    intro c hc
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨hUniverseCode s hs, hFiberCode s hs⟩
  have hInj : Set.InjOn code (↑states : Set β) := by
    intro s hs t ht hCode
    have hFirst : universeCode (universeOf s) = universeCode (universeOf t) :=
      congrArg Prod.fst hCode
    have hSecond : fiberCode s = fiberCode t := congrArg Prod.snd hCode
    exact hSeparates s hs t ht hFirst hSecond
  calc
    states.card = (states.image code).card :=
      (Finset.card_image_iff.mpr hInj).symm
    _ ≤ (twoLevelCharges U large small).card := Finset.card_le_card hImage
    _ = (U.card * large.card) * (U.card * small.card) :=
      twoLevelCharges_card U large small

end IrrRAFEnumeration

import proofs.PowerLawSmallRAF.BinarySourceEnumeration
import proofs.HordijkSteelThreshold.PolymerCounts

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- In the split-position model, the product word together with the left
factor length uniquely determines the base reaction channel. -/
theorem binaryReaction_eq_of_product_eq_of_leftLength_eq {n : Nat}
    {left right : Reaction n}
    (hproduct : reactionProduct left = reactionProduct right)
    (hlength : reactionLeftLength left = reactionLeftLength right) :
    left = right := by
  rcases left with ⟨leftIndex, leftWord, leftSplit⟩
  rcases right with ⟨rightIndex, rightWord, rightSplit⟩
  change (⟨leftIndex, leftWord⟩ : Molecule n) =
    (⟨rightIndex, rightWord⟩ : Molecule n) at hproduct
  obtain ⟨hindex, hwordHeq⟩ := Sigma.mk.inj_iff.mp hproduct
  subst rightIndex
  have hword : leftWord = rightWord := eq_of_heq hwordHeq
  subst rightWord
  congr
  apply Fin.ext
  dsimp [reactionLeftLength] at hlength
  omega

/-- The split-position reaction sigma-type has exactly the source reaction
count used by the power-law degree model. -/
theorem card_binaryReaction_eq_sourceReactionCount {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = sourceReactionCount n := by
  simpa only [sourceReactionCount] using
    (HordijkSteelThreshold.card_reactions_exact hn)

/-- Exact enumeration of all nongateway split-position reaction channels. -/
noncomputable def binaryNongatewayReactionEquivFin {n : Nat} (hn : 2 ≤ n)
    (gateway : Reaction n) :
    {r : Reaction n // r ≠ gateway} ≃ Fin (sourceReactionCount n - 1) :=
  (Fintype.equivFin {r : Reaction n // r ≠ gateway}).trans
    (finCongr (by
      calc
        Fintype.card {r : Reaction n // r ≠ gateway} =
            Fintype.card (Reaction n) - 1 := Set.card_ne_eq gateway
        _ = sourceReactionCount n - 1 := by
          rw [card_binaryReaction_eq_sourceReactionCount hn]))

/-- Encode every member of an injective reaction family except its displayed
gateway member into the exact `R_n-1` nongateway catalogue. -/
noncomputable def encodedNongatewayFamily {n instructionCount : Nat}
    (hn : 2 ≤ n) (reaction : Fin instructionCount → Reaction n)
    (hinjective : Function.Injective reaction) (gatewayIndex : Fin instructionCount) :
    Finset (Fin (sourceReactionCount n - 1)) :=
  Finset.univ.image fun index : {i : Fin instructionCount // i ≠ gatewayIndex} =>
    binaryNongatewayReactionEquivFin hn (reaction gatewayIndex)
      ⟨reaction index, fun heq => index.property (hinjective heq)⟩

/-- Removing the gateway from an injective `s`-reaction shelling leaves
exactly `s-1` distinct nongateway channel requirements. -/
theorem card_encodedNongatewayFamily {n instructionCount : Nat}
    (hn : 2 ≤ n) (reaction : Fin instructionCount → Reaction n)
    (hinjective : Function.Injective reaction) (gatewayIndex : Fin instructionCount) :
    (encodedNongatewayFamily hn reaction hinjective gatewayIndex).card =
      instructionCount - 1 := by
  rw [encodedNongatewayFamily, Finset.card_image_of_injective]
  · rw [Finset.card_univ]
    simpa only [Fintype.card_fin] using (Set.card_ne_eq gatewayIndex)
  · intro left right heq
    apply Subtype.ext
    apply hinjective
    exact congrArg Subtype.val
      ((binaryNongatewayReactionEquivFin hn (reaction gatewayIndex)).injective heq)

theorem encodedNongatewayFamily_congr {n instructionCount : Nat}
    (hn : 2 ≤ n) {first second : Fin instructionCount → Reaction n}
    (hfirst : Function.Injective first) (hsecond : Function.Injective second)
    {firstGateway secondGateway : Fin instructionCount}
    (hreaction : first = second) (hgateway : firstGateway = secondGateway) :
    encodedNongatewayFamily hn first hfirst firstGateway =
      encodedNongatewayFamily hn second hsecond secondGateway := by
  subst second
  subst secondGateway
  rfl

/-- A total canonical `q`-element subset of `Fin R` whenever `q ≤ R`. -/
def initialFinset (R q : Nat) : Finset (Fin R) :=
  if hqR : q ≤ R then
    Finset.univ.image (Fin.castLE hqR)
  else
    ∅

theorem card_initialFinset_of_le {R q : Nat} (hqR : q ≤ R) :
    (initialFinset R q).card = q := by
  rw [initialFinset, dif_pos hqR, Finset.card_image_of_injective]
  · simp
  · exact Fin.castLE_injective hqR

end PowerLawSmallRAF

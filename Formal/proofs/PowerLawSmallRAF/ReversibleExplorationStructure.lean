import proofs.RAF.Concrete.PolymerCRS

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

private theorem reaction_eq_of_product_eq_of_leftLength_eq {n : Nat}
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

/-- The two factors uniquely identify a binary split-position reaction. -/
theorem binaryReaction_eq_of_left_eq_of_right_eq {n : Nat}
    {first second : Reaction n}
    (hleft : reactionLeft first = reactionLeft second)
    (hright : reactionRight first = reactionRight second) :
    first = second := by
  rcases first with ⟨firstIndex, firstWord, firstSplit⟩
  rcases second with ⟨secondIndex, secondWord, secondSplit⟩
  have hleftLength := congrArg molLength hleft
  have hrightLength := congrArg molLength hright
  simp only [molLength_reactionLeft, molLength_reactionRight,
    reactionLeftLength, reactionRightLength] at hleftLength hrightLength
  have hindex : firstIndex = secondIndex := by
    apply Fin.ext
    omega
  subst secondIndex
  have hsplit : firstSplit = secondSplit := by
    apply Fin.ext
    omega
  subst secondSplit
  congr
  have hleftCode : (splitCodes
      (⟨firstIndex, firstWord, firstSplit⟩ : Reaction n)).1 =
      (splitCodes
      (⟨firstIndex, secondWord, firstSplit⟩ : Reaction n)).1 := by
    obtain ⟨_, hcode⟩ := Sigma.mk.inj_iff.mp hleft
    apply Fin.ext
    simpa only [reactionLeft, moleculeOfCode] using
      congrArg Fin.val (eq_of_heq hcode)
  have hrightCode : (splitCodes
      (⟨firstIndex, firstWord, firstSplit⟩ : Reaction n)).2 =
      (splitCodes
      (⟨firstIndex, secondWord, firstSplit⟩ : Reaction n)).2 := by
    obtain ⟨_, hcode⟩ := Sigma.mk.inj_iff.mp hright
    apply Fin.ext
    simpa only [reactionRight, moleculeOfCode] using
      congrArg Fin.val (eq_of_heq hcode)
  have hpairs : splitCodes
      (⟨firstIndex, firstWord, firstSplit⟩ : Reaction n) =
      splitCodes (⟨firstIndex, secondWord, firstSplit⟩ : Reaction n) :=
    Prod.ext hleftCode hrightCode
  have hcast := (Equiv.injective finProdFinEquiv.symm) hpairs
  apply Fin.ext
  simpa using congrArg (fun z => z.val) hcast

/-- Reactions whose ligation direction is enabled by `available`. -/
abbrev LigationEnabledReaction {n : Nat} (available : Finset (Molecule n)) :=
  {r : Reaction n // reactionLeft r ∈ available ∧ reactionRight r ∈ available}

/-- Reactions whose cleavage direction is enabled by `available`. -/
abbrev CleavageEnabledReaction {n : Nat} (available : Finset (Molecule n)) :=
  {r : Reaction n // reactionProduct r ∈ available}

def ligationEnabledReactionCode {n : Nat} {available : Finset (Molecule n)}
    (r : LigationEnabledReaction available) :
    {x // x ∈ available} × {x // x ∈ available} :=
  (⟨reactionLeft r, r.property.1⟩, ⟨reactionRight r, r.property.2⟩)

theorem ligationEnabledReactionCode_injective {n : Nat}
    {available : Finset (Molecule n)} :
    Function.Injective (@ligationEnabledReactionCode n available) := by
  intro first second h
  apply Subtype.ext
  apply binaryReaction_eq_of_left_eq_of_right_eq
  · exact congrArg (fun p => p.1.val) h
  · exact congrArg (fun p => p.2.val) h

def cleavageEnabledReactionCode {n : Nat} {available : Finset (Molecule n)}
    (r : CleavageEnabledReaction available) :
    {x // x ∈ available} × Fin n :=
  (⟨reactionProduct r, r.property⟩,
    ⟨r.val.2.2.val, r.val.2.2.isLt.trans r.val.1.isLt⟩)

theorem cleavageEnabledReactionCode_injective {n : Nat}
    {available : Finset (Molecule n)} :
    Function.Injective (@cleavageEnabledReactionCode n available) := by
  intro first second h
  apply Subtype.ext
  apply reaction_eq_of_product_eq_of_leftLength_eq
  · exact congrArg (fun p => p.1.val) h
  · have hsplit : first.val.2.2.val = second.val.2.2.val :=
      congrArg (fun p => p.2.val) h
    dsimp [reactionLeftLength]
    omega

theorem card_ligationEnabledReaction_le {n : Nat}
    (available : Finset (Molecule n)) :
    Fintype.card (LigationEnabledReaction available) ≤ available.card ^ 2 := by
  calc
    Fintype.card (LigationEnabledReaction available) ≤
        Fintype.card ({x // x ∈ available} × {x // x ∈ available}) :=
      Fintype.card_le_of_injective ligationEnabledReactionCode
        ligationEnabledReactionCode_injective
    _ = available.card ^ 2 := by simp [pow_two]

theorem card_cleavageEnabledReaction_le {n : Nat}
    (available : Finset (Molecule n)) :
    Fintype.card (CleavageEnabledReaction available) ≤ available.card * n := by
  calc
    Fintype.card (CleavageEnabledReaction available) ≤
        Fintype.card ({x // x ∈ available} × Fin n) :=
      Fintype.card_le_of_injective cleavageEnabledReactionCode
        cleavageEnabledReactionCode_injective
    _ = available.card * n := by simp

/-- A reaction is reversibly enabled when either its two factors or its
product is already available. -/
abbrev ReversiblyEnabledReaction {n : Nat} (available : Finset (Molecule n)) :=
  {r : Reaction n //
    (reactionLeft r ∈ available ∧ reactionRight r ∈ available) ∨
      reactionProduct r ∈ available}

def reversiblyEnabledReactionFinset {n : Nat}
    (available : Finset (Molecule n)) : Finset (Reaction n) :=
  Finset.univ.filter fun r =>
    (reactionLeft r ∈ available ∧ reactionRight r ∈ available) ∨
      reactionProduct r ∈ available

theorem card_reversiblyEnabledReaction_le {n : Nat}
    (available : Finset (Molecule n)) :
    Fintype.card (ReversiblyEnabledReaction available) ≤
      available.card ^ 2 + available.card * n := by
  let ligation : Finset (Reaction n) := Finset.univ.filter fun r =>
    reactionLeft r ∈ available ∧ reactionRight r ∈ available
  let cleavage : Finset (Reaction n) := Finset.univ.filter fun r =>
    reactionProduct r ∈ available
  let revEquiv : ReversiblyEnabledReaction available ≃
      {r // r ∈ ligation ∪ cleavage} :=
    { toFun := fun r => ⟨r.val, by
        rw [Finset.mem_union]
        rcases r.property with h | h
        · left
          simpa only [ligation, Finset.mem_filter, Finset.mem_univ,
            true_and] using h
        · right
          simpa only [cleavage, Finset.mem_filter, Finset.mem_univ,
            true_and] using h⟩
      invFun := fun r => ⟨r.val, by
        have hr := r.property
        rw [Finset.mem_union] at hr
        rcases hr with h | h
        · left
          simpa only [ligation, Finset.mem_filter, Finset.mem_univ,
            true_and] using h
        · right
          simpa only [cleavage, Finset.mem_filter, Finset.mem_univ,
            true_and] using h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let ligEquiv : LigationEnabledReaction available ≃ {r // r ∈ ligation} :=
    { toFun := fun r => ⟨r.val, by
        simpa only [ligation, Finset.mem_filter, Finset.mem_univ,
          true_and] using r.property⟩
      invFun := fun r => ⟨r.val, by
        simpa only [ligation, Finset.mem_filter, Finset.mem_univ,
          true_and] using r.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let cleavEquiv : CleavageEnabledReaction available ≃ {r // r ∈ cleavage} :=
    { toFun := fun r => ⟨r.val, by
        simpa only [cleavage, Finset.mem_filter, Finset.mem_univ,
          true_and] using r.property⟩
      invFun := fun r => ⟨r.val, by
        simpa only [cleavage, Finset.mem_filter, Finset.mem_univ,
          true_and] using r.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Fintype.card (ReversiblyEnabledReaction available) =
        (ligation ∪ cleavage).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr revEquiv
    _ ≤ ligation.card + cleavage.card := Finset.card_union_le ligation cleavage
    _ = Fintype.card (LigationEnabledReaction available) +
        Fintype.card (CleavageEnabledReaction available) := by
      rw [← Fintype.card_coe ligation, ← Fintype.card_coe cleavage,
        Fintype.card_congr ligEquiv, Fintype.card_congr cleavEquiv]
    _ ≤ available.card ^ 2 + available.card * n :=
      Nat.add_le_add (card_ligationEnabledReaction_le available)
        (card_cleavageEnabledReaction_le available)

theorem card_reversiblyEnabledReactionFinset_le {n : Nat}
    (available : Finset (Molecule n)) :
    (reversiblyEnabledReactionFinset available).card ≤
      available.card ^ 2 + available.card * n := by
  have hequiv : ReversiblyEnabledReaction available ≃
      {r // r ∈ reversiblyEnabledReactionFinset available} :=
    { toFun := fun r => ⟨r.val, by
        simpa only [reversiblyEnabledReactionFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using r.property⟩
      invFun := fun r => ⟨r.val, by
        simpa only [reversiblyEnabledReactionFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using r.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    (reversiblyEnabledReactionFinset available).card =
        Fintype.card {r // r ∈ reversiblyEnabledReactionFinset available} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (ReversiblyEnabledReaction available) :=
      Fintype.card_congr hequiv.symm
    _ ≤ available.card ^ 2 + available.card * n :=
      card_reversiblyEnabledReaction_le available

end PowerLawSmallRAF

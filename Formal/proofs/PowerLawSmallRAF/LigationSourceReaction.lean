import proofs.PowerLawSmallRAF.LigationWordCode

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete

theorem sourceMolecule_eq_of_length_code {n : Nat} {x y : Molecule n}
    (hlen : molLength x = molLength y) (hcode : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨⟨kx, hkx⟩, cx⟩
  rcases y with ⟨⟨ky, hky⟩, cy⟩
  have hk : kx = ky := by simpa [molLength] using hlen
  subst ky
  have hc : cx = cy := Fin.ext hcode
  subst cy
  rfl

/-- Each actual split position is retained as a separate source channel. -/
def ligationCutReaction (n : Nat) (w : LigationWord) (hn : w.length ≤ n)
    (i : ligationCuts w) : Reaction n :=
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  ⟨⟨w.length-1, by omega⟩,
    ⟨⟨ligationWordCode w, by
        simpa only [Nat.sub_add_cancel (show 1 ≤ w.length by omega)] using ligationWordCode_lt w⟩,
      ⟨i.val-1, by change i.val-1 < w.length-1; omega⟩⟩⟩

@[simp] theorem ligationCutReaction_product_length (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w) :
    reactionProductLength (ligationCutReaction n w hn i) = w.length := by
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  dsimp [reactionProductLength, ligationCutReaction]
  omega

@[simp] theorem ligationCutReaction_left_length (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w) :
    reactionLeftLength (ligationCutReaction n w hn i) = i.val := by
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  dsimp [reactionLeftLength, ligationCutReaction]
  omega

@[simp] theorem ligationCutReaction_right_length (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w) :
    reactionRightLength (ligationCutReaction n w hn i) = w.length-i.val := by
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  dsimp [reactionRightLength, ligationCutReaction]
  omega

theorem ligationCutReaction_product (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w) (h0 : 1 ≤ w.length) :
    reactionProduct (ligationCutReaction n w hn i) = ligationWordMolecule n w h0 hn := by
  apply sourceMolecule_eq_of_length_code
  · simp
  · rfl

theorem ligationWordCode_take_drop (w : LigationWord) (i : Nat) :
    ligationWordCode w = ligationWordCode (w.drop i) +
      2^(w.drop i).length*ligationWordCode (w.take i) := by
  simpa only [List.take_append_drop] using ligationWordCode_append (w.take i) (w.drop i)

theorem ligationCutReaction_left (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w)
    (h0 : 1 ≤ (w.take i.val).length) (hbound : (w.take i.val).length ≤ n) :
    reactionLeft (ligationCutReaction n w hn i) = ligationWordMolecule n (w.take i.val) h0 hbound := by
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  apply sourceMolecule_eq_of_length_code
  · simp [List.length_take, Nat.min_eq_left hi.2.le]
  · change ligationWordCode w / 2^reactionRightLength (ligationCutReaction n w hn i) = _
    rw [ligationCutReaction_right_length]
    change ligationWordCode w / 2^(w.length-i.val) = ligationWordCode (w.take i.val)
    have hs := ligationWordCode_take_drop w i.val
    have hb := ligationWordCode_lt (w.drop i.val)
    rw [List.length_drop] at hs hb
    rw [hs, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hb, zero_add]

theorem ligationCutReaction_right (n : Nat) (w : LigationWord)
    (hn : w.length ≤ n) (i : ligationCuts w)
    (h0 : 1 ≤ (w.drop i.val).length) (hbound : (w.drop i.val).length ≤ n) :
    reactionRight (ligationCutReaction n w hn i) = ligationWordMolecule n (w.drop i.val) h0 hbound := by
  apply sourceMolecule_eq_of_length_code
  · simp
  · change ligationWordCode w % 2^reactionRightLength (ligationCutReaction n w hn i) = _
    rw [ligationCutReaction_right_length]
    change ligationWordCode w % 2^(w.length-i.val) = ligationWordCode (w.drop i.val)
    have hs := ligationWordCode_take_drop w i.val
    have hb := ligationWordCode_lt (w.drop i.val)
    rw [List.length_drop] at hs hb
    rw [hs, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

/-- Equal source channels force equal words and equal split indices. -/
theorem ligationCutReaction_injective (n : Nat) (u v : LigationWord)
    (hun : u.length ≤ n) (hvn : v.length ≤ n)
    (i : ligationCuts u) (j : ligationCuts v)
    (h : ligationCutReaction n u hun i = ligationCutReaction n v hvn j) :
    u = v ∧ i.val = j.val := by
  have hl : u.length = v.length := by
    simpa using congrArg reactionProductLength h
  have hc : ligationWordCode u = ligationWordCode v :=
    congrArg (fun r : Reaction n => r.2.1.val) h
  refine ⟨ligationWordCode_injective_of_length hl hc, ?_⟩
  simpa using congrArg reactionLeftLength h

end PowerLawSmallRAF

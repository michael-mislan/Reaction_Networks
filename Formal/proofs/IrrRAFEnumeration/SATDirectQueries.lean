import proofs.IrrRAFEnumeration.SATLocalBits

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource RAF

def inputBit {n m : Nat} :
    Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)) →
    Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)) → Bool
  | .inl _, .food => true
  | .inr j, .wire v => if h : j.val < Fintype.card (Step n m) then
      needBit ((stepCode n m).symm ⟨j.val,h⟩) ((wireCode n m).symm v)
    else decide (v = wireCode n m .output)
  | _, _ => false

def outputWork {n m : Nat} (hit : Fin m → Choice n → Bool × Nat) :
    Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)) →
    Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)) → Bool × Nat
  | .inl i, .wire v => (decide (v = wireCode n m (.literal ((inputCode n).symm i))), 0)
  | .inr j, .marker k => (decide (k = j), 0)
  | .inr j, .wire v => if h : j.val < Fintype.card (Step n m) then
      produceWork hit ((stepCode n m).symm ⟨j.val,h⟩) ((wireCode n m).symm v)
    else (true, 0)
  | _, _ => (false, 0)

theorem produceWork_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (hit : Fin m → Choice n → Bool × Nat)
    (h : ∀ j x, (hit j x).1 = true ↔ x ∈ Φ j) (s : Step n m) (v : Wire n m) :
    (produceWork hit s v).1 = true ↔ v ∈ produces Φ s := by
  rw [produceWork_value]
  have he : (fun j x => (hit j x).1) = (fun j x => decide (x ∈ Φ j)) := by
    funext j x
    apply Bool.eq_iff_iff.mpr
    simpa using h j x
  rw [he]
  exact produceBit_correct Φ s v

theorem inputBit_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    inputBit r x = true ↔ x ∈ (crs (rules Φ)).inputs r := by
  cases r with
  | inl i => cases x <;> simp [inputBit, crs]
  | inr j =>
      by_cases hj : j.val < Fintype.card (Step n m)
      · cases x with
        | food => simp [inputBit, crs, hj]
        | marker k => simp [inputBit, crs, hj]
        | wire k =>
            obtain ⟨v,rfl⟩ := (wireCode n m).surjective k
            simpa [inputBit, crs, rules, hj, Finset.mem_image] using
              needBit_correct ((stepCode n m).symm ⟨j.val,hj⟩) v
      · cases x <;> simp [inputBit, crs, rules, hj]

theorem outputWork_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (hit : Fin m → Choice n → Bool × Nat)
    (h : ∀ j x, (hit j x).1 = true ↔ x ∈ Φ j)
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    (outputWork hit r x).1 = true ↔ x ∈ (crs (rules Φ)).outputs r := by
  cases r with
  | inl i => cases x <;> simp [outputWork, crs, rules]
  | inr j =>
      by_cases hj : j.val < Fintype.card (Step n m)
      · cases x with
        | food => simp [outputWork, crs, hj]
        | marker k => simp [outputWork, crs, hj]
        | wire k =>
            obtain ⟨v,rfl⟩ := (wireCode n m).surjective k
            simpa [outputWork, crs, rules, hj, Finset.mem_image] using
              produceWork_correct Φ hit h ((stepCode n m).symm ⟨j.val,hj⟩) v
      · cases x <;> simp [outputWork, crs, hj]

theorem outputWork_cost {n m : Nat} (hit : Fin m → Choice n → Bool × Nat)
    (B : Nat) (h : ∀ j x, (hit j x).2 ≤ B)
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))
    (x : Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :
    (outputWork hit r x).2 ≤ B := by
  cases r with
  | inl i => cases x <;> simp [outputWork]
  | inr j =>
      cases x with
      | food => simp [outputWork]
      | marker k => simp [outputWork]
      | wire v =>
          dsimp only [outputWork]
          split_ifs
          · exact produceWork_cost hit B h _ _
          · exact Nat.zero_le _

/-- All incidence queries now use direct pattern matching. The recorded cost
is the actual input-list traversal, excluding fixed arithmetic and output writes. -/
def datumWork {n m : Nat} (hit : Fin m → Choice n → Bool × Nat) :
    Slot (moleculeCount n m) (reactionCount n m) → Bool × Nat
  | .inl x => (decide ((moleculeCode _ _).symm x = .food), 0)
  | .inr (r,c,x) =>
      let rx := (reactionCode _ _).symm r
      let mol := (moleculeCode _ _).symm x
      if c = 0 then (inputBit rx mol, 0)
      else if c = 1 then outputWork hit rx mol
      else (decide (mol = Molecule.marker (catalystIndex rx)), 0)

theorem datumWork_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (hit : Fin m → Choice n → Bool × Nat)
    (h : ∀ j x, (hit j x).1 = true ↔ x ∈ Φ j)
    (z : Slot (moleculeCount n m) (reactionCount n m)) :
    (datumWork hit z).1 = datum Φ z := by
  apply Bool.eq_iff_iff.mpr
  cases z with
  | inl x => simp [datumWork, datum, crs]
  | inr z =>
      rcases z with ⟨r,c,x⟩
      by_cases hc : c = 0
      · simp [datumWork, datum, hc, inputBit_correct Φ]
      · by_cases hd : c = 1
        · simp [datumWork, datum, hd, outputWork_correct Φ hit h]
        · simp [datumWork, datum, hc, hd]

theorem datumWork_cost {n m : Nat} (body : List Bool)
    (z : Slot (moleculeCount n m) (reactionCount n m)) :
    (datumWork (clauseWork n m body) z).2 ≤ body.length+1 := by
  cases z with
  | inl x => simp [datumWork]
  | inr z =>
      rcases z with ⟨r,c,x⟩
      dsimp only [datumWork]
      split_ifs
      · exact Nat.zero_le _
      · exact outputWork_cost _ _ (fun _ _ => readBitWork_cost _ _) _ _
      · exact Nat.zero_le _

end IrrRAFEnumeration.SATSource

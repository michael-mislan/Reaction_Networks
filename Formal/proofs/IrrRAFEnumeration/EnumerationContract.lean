import proofs.IrrRAFEnumeration.SourceCountContract

namespace IrrRAFEnumeration.EnumerationContract
open Complexity Complexity.TM RAF SATSource SATCompletion CircuitSource

variable {M R : Type} [DecidableEq M] [DecidableEq R] {a b : Nat}

/-- Dense food/input/output/catalyst encoding with explicit finite identifiers. -/
def incidence (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (em : M ≃ Fin a) (er : R ≃ Fin b) : Slot a b → Bool
  | .inl x => decide (em.symm x ∈ Q.food)
  | .inr (r,c,x) =>
    if c = 0 then decide (em.symm x ∈ Q.inputs (er.symm r))
    else if c = 1 then decide (em.symm x ∈ Q.outputs (er.symm r))
    else decide (C (em.symm x) (er.symm r))

def inputBits (Q : CRS M R) (C : Catalysis M R) [DecidableRel C]
    (em : M ≃ Fin a) (er : R ≃ Fin b) : List Bool :=
  List.replicate a true ++ [false] ++ List.replicate b true ++ [false] ++
    List.ofFn (fun i => incidence Q C em er ((slotCode a b).symm i))

def outputBody (er : R ≃ Fin b) (rows : List (Finset R)) : List Bool :=
  rows.flatMap (fun S => List.ofFn (fun i : Fin b => decide (er.symm i ∈ S)))

def outputBits (er : R ≃ Fin b) (rows : List (Finset R)) : List Bool :=
  List.replicate rows.length true ++ false :: outputBody er rows

theorem outputBody_length (er : R ≃ Fin b) (rows : List (Finset R)) :
    (outputBody er rows).length = rows.length*b := by
  induction rows with
  | nil => simp [outputBody]
  | cons S rows ih =>
    change (List.ofFn (fun i : Fin b => decide (er.symm i ∈ S)) ++ outputBody er rows).length = (rows.length+1)*b
    rw [List.length_append,List.length_ofFn,ih,Nat.add_mul,Nat.one_mul]
    omega

theorem outputBits_length (er : R ≃ Fin b) (rows : List (Finset R)) :
    (outputBits er rows).length = fixedWidthOutputLength b rows.length := by
  simp only [outputBits,List.length_append,List.length_replicate,List.length_cons,outputBody_length]
  unfold fixedWidthOutputLength
  omega

/-- Uniform exact output-polynomial enumeration. The finite labelings specify
the input bits; they are not advice supplied separately to the fixed machine.
Every finite ordinary CRS and every explicit labeling is covered. -/
def Enumerates {k : Nat} (E : TM k) (p : Polynomial Nat) : Prop :=
  ∀ (M R : Type) [DecidableEq M] [DecidableEq R] [Fintype R]
    (a b : Nat) (em : M ≃ Fin a) (er : R ≃ Fin b)
    (Q : CRS M R) (C : Catalysis M R) [DecidableRel C],
    ∃ (rows : List (Finset R)) (c : Cfg k E.Q) (t : Nat),
      rows.Nodup ∧ rows.toFinset = irrRAFFamily Q C ∧
      t ≤ p.eval ((inputBits Q C em er).length+(outputBits er rows).length) ∧
      E.reachesIn t (E.initCfg (inputBits Q C em er)) c ∧ E.halted c ∧
      c.output.HasOutput (outputBits er rows)

def OutputPolynomialEnumeration : Prop := ∃ (k : Nat) (E : TM k) (p : Polynomial Nat), Enumerates E p

theorem source_input_eq {n m : Nat} (Φ : Fin m → Finset (Choice n))
    [DecidableRel (catalysis : Catalysis
      (Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))
      (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))))] :
    inputBits (crs (rules Φ)) catalysis
      (moleculeCode _ _) (reactionCode _ _) = sourceBits Φ := by
  have hd : ∀ z, incidence (crs (rules Φ)) catalysis
      (moleculeCode _ _) (reactionCode _ _) z = datum Φ z := by
    intro z
    cases z with
    | inl x => rfl
    | inr v =>
      rcases v with ⟨r,c,x⟩
      simp only [incidence,datum,catalysis]
      congr 2
      apply decide_eq_decide.mpr
      rfl
  simp only [inputBits,sourceBits,sourceBody,hd,moleculeCount,reactionCount]
  congr 1

theorem Enumerates.sourceCountBound {k : Nat} {E : TM k} {p : Polynomial Nat}
    (hE : Enumerates E p) : SourceCountBound E p := by
  intro n m Φ _
  letI : DecidableRel (catalysis : Catalysis
      (Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))
      (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))) :=
    fun x r => inferInstanceAs (Decidable (x = Molecule.marker (catalystIndex r)))
  obtain ⟨rows,c,t,hnd,hrows,ht,hr,hh,ho⟩ := hE _ _ (moleculeCount n m) (reactionCount n m)
    (moleculeCode _ _) (reactionCode _ _) (crs (rules Φ)) catalysis
  have hlen : rows.length = sourceCount Φ := by
    rw [sourceCount,← hrows]
    exact (List.toFinset_card_of_nodup hnd).symm
  have hin := source_input_eq Φ
  have hin' : inputBits (crs (rules Φ)) catalysis (moleculeCode _ _) (reactionCode _ _) = sourceBits Φ := by
    convert hin using 1
  erw [hin'] at ht hr
  rw [outputBits_length,hlen] at ht
  refine ⟨outputBody (reactionCode _ _) rows,c,t,?_,ht,hr,hh,?_⟩
  · rw [outputBody_length,hlen]
    rfl
  · simpa only [outputBits,hlen] using ho

end IrrRAFEnumeration.EnumerationContract

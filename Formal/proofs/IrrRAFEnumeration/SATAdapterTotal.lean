import proofs.IrrRAFEnumeration.SATAdapterStarted
import proofs.Complexitylib.Classes.P.NormalForm

namespace IrrRAFEnumeration.SATSource
open Complexity SAT SATCompletion Complexity.TM

def invalidRectangle : List Bool := cnfBits (fun _ : Fin 1 => (∅ : Finset (Choice 2)))
def invalidAdapterBranchTM : TM 4 := seqTM branchPrepareTM (emitBitsTM invalidRectangle)
def branchPre (z : List Bool) (b : Bool) (inp : Tape) (work : Fin 4 → Tape) (out : Tape) :=
  inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ inp.head = z.length+1 ∧
    work = (fun _ => regTape 0) ∧ out = syntaxVerdict b

theorem invalidAdapterBranchTM_correct (z : List Bool) :
    invalidAdapterBranchTM.HoareTime (branchPre z false)
      (fun _ _ out => out.HasOutput invalidRectangle ∧ out.StartInvariant) (z.length+15) := by
  have h := seqTM_hoareTime _ _ (branchPrepareTM_correct z false)
    (emitPred_transition (parked_init_input z) (fun _ => parked_regTape 0) [])
    (emitBitsTM_hoareTime invalidRectangle ⟨1,(Tape.init (z.map Γ.ofBool)).cells⟩
      (fun _ : Fin 4 => regTape 0) [] (parked_init_input z) (fun _ => parked_regTape 0))
  intro inp work out hpre
  obtain ⟨c,t,ht,hr,hh,_,_,ho⟩ := h inp work out hpre
  have hl : invalidRectangle.length = 9 := by decide
  refine ⟨c,t,by simpa only [hl] using ht,hr,hh,?_,ho.2.1,ho.parked.2⟩
  simpa only [List.nil_append] using ho.hasOutput

theorem syntaxPost_transition (z : List Bool) (inp : Tape) (work : Fin 4 → Tape) (out : Tape)
    (h : syntaxPost z inp work out) :
    syntaxPost z (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ := by
  rcases h with ⟨hc,hh,rfl,rfl⟩
  have hp : Parked inp := ⟨by omega,by rw [hc]; exact Tape.init_ofBool_cells_ne_start z⟩
  exact ⟨by rw [hp.transitionInput_eq_self]; exact hc,
    by rw [hp.transitionInput_eq_self]; exact hh,
    funext (fun _ => (parked_regTape 0).transitionTape_eq_self),rfl⟩

def totalRectangleAdapterTM : TM 4 := ifTM syntaxTestTM validAdapterBranchTM invalidAdapterBranchTM

/-- Total, uniform polynomial-time implementation of the exact raw-string
adapter. Malformed encodings map to the fixed unsatisfiable rectangle. -/
theorem totalRectangleAdapterTM_correct (z : List Bool) :
    totalRectangleAdapterTM.HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (fun _ _ out => out.HasOutput (librarySATAdapter z)) (2000*(z.length+2)^3) := by
  have hthen : validAdapterBranchTM.HoareTime
      (fun inp work out => branchPre z true inp work out ∧ (CNF.decode? z).isSome = true)
      (fun _ _ out => out.HasOutput (librarySATAdapter z) ∧ out.StartInvariant)
      (z.length+6+1000*(z.length+2)^3) := by
    rintro inp work out ⟨hpre,hvalid⟩
    cases hd : CNF.decode? z with
    | none => simp [hd] at hvalid
    | some φ =>
      have hz := CNF.decode?_sound hd
      subst z
      simpa only [librarySATAdapter,CNF.decode?_encode] using
        validAdapterBranchTM_correct φ inp work out hpre
  have helse : invalidAdapterBranchTM.HoareTime
      (fun inp work out => branchPre z false inp work out ∧ (CNF.decode? z).isSome = false)
      (fun _ _ out => out.HasOutput (librarySATAdapter z) ∧ out.StartInvariant)
      (z.length+15) := by
    rintro inp work out ⟨hpre,hvalid⟩
    cases hd : CNF.decode? z with
    | some φ => simp [hd] at hvalid
    | none => simpa only [librarySATAdapter,hd,invalidRectangle] using
        invalidAdapterBranchTM_correct z inp work out hpre
  have hwf : ∀ inp work out, syntaxPost z inp work out → AllTapesWF inp work out := by
    rintro inp work out ⟨hc,_,rfl,rfl⟩
    exact ⟨by rw [hc]; rfl,by rw [hc]; exact Tape.init_ofBool_cells_ne_start z,
      fun _ => rfl,fun _ => (parked_regTape 0).2,
      (syntaxVerdict_startInvariant _).1,(syntaxVerdict_startInvariant _).2⟩
  have hhead : ∀ inp work out, syntaxPost z inp work out → out.head ≤ 1 := by
    rintro inp work out ⟨_,_,_,rfl⟩
    exact le_refl _
  have hyes : ∀ inp work out, syntaxPost z inp work out → out.cells 1 = Γ.one →
      branchPre z true (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ ∧
        (CNF.decode? z).isSome = true := by
    intro inp work out h hv
    have he : Γ.ofBool (CNF.decode? z).isSome = Γ.one := by
      rw [h.2.2.2,syntaxVerdict_cell] at hv
      exact hv
    have hb : (CNF.decode? z).isSome = true := by
      cases hq : (CNF.decode? z).isSome <;> simp_all [Γ.ofBool]
    have hs := syntaxPost_transition z inp work out h
    rw [syntaxPost,hb] at hs
    exact ⟨hs,hb⟩
  have hno : ∀ inp work out, syntaxPost z inp work out → out.cells 1 ≠ Γ.one →
      branchPre z false (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ ∧
        (CNF.decode? z).isSome = false := by
    intro inp work out h hv
    have he : Γ.ofBool (CNF.decode? z).isSome ≠ Γ.one := by
      rw [h.2.2.2,syntaxVerdict_cell] at hv
      exact hv
    have hb : (CNF.decode? z).isSome = false := by
      cases hq : (CNF.decode? z).isSome <;> simp_all [Γ.ofBool]
    have hs := syntaxPost_transition z inp work out h
    rw [syntaxPost,hb] at hs
    exact ⟨hs,hb⟩
  have hpost : ∀ (inp : Tape) (work : Fin 4 → Tape) (out : Tape),
      out.HasOutput (librarySATAdapter z) ∧ out.StartInvariant →
      (fun (_ : Tape) (_ : Fin 4 → Tape) (o : Tape) => o.HasOutput (librarySATAdapter z))
        (transitionInput inp) (fun i => transitionTape (work i)) (transitionTape out) := by
    rintro inp work out ⟨ho,hinv⟩
    exact (Tape.hasOutput_congr (transitionTape_cells out hinv.2) _).mpr ho
  have h := ifTM_hoareTime syntaxTestTM validAdapterBranchTM invalidAdapterBranchTM
    (post := fun _ _ out => out.HasOutput (librarySATAdapter z))
    (syntaxTestTM_correct z) hwf hhead hyes hno hthen helse hpost hpost
  apply h.mono_bound
  have hp := Nat.pow_le_pow_right (show 1 ≤ z.length+2 by omega) (by decide : 1 ≤ 3)
  simp only [pow_one] at hp
  omega

theorem totalRectangleAdapterTM_computes : totalRectangleAdapterTM.ComputesInTime
    librarySATAdapter (fun L => 2000*(L+2)^3) := by
  intro z
  exact totalRectangleAdapterTM_correct z _ _ _ ⟨rfl,rfl,rfl⟩

theorem librarySATAdapter_mem_FP : librarySATAdapter ∈ FP := by
  apply mem_FP_iff_computesInTime_polynomial.mpr
  refine ⟨4,totalRectangleAdapterTM,Polynomial.C 2000*(Polynomial.X+Polynomial.C 2)^3,?_⟩
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X] using totalRectangleAdapterTM_computes

end IrrRAFEnumeration.SATSource

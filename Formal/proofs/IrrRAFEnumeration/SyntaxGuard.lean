import proofs.IrrRAFEnumeration.GuardPreparation
import proofs.IrrRAFEnumeration.SATLibraryAdapterSpec

namespace IrrRAFEnumeration.SyntaxGuard
open Complexity SAT Complexity.TM SATSource GuardPreparation
variable {n : Nat}

def syntaxCheckTM (n : Nat) : TM n := (Nat.zero_add n) ▸ syntaxTM.liftTM n

theorem syntax_check_correct (n : Nat) (z : List Bool) :
    (syntaxCheckTM n).HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (guardPre n z (CNF.decode? z).isSome) (z.length+2) := by
  have hbase : (syntaxTM.liftTM n).HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (guardPre (0+n) z (CNF.decode? z).isSome) (z.length+2) := by
    rintro inp work out ⟨rfl,rfl,rfl⟩
    obtain ⟨c,hr,hh,hc,hp,ho⟩ := syntaxTM_initial_boundary z
    have h := liftTM_reachesIn_initCfg_of_pos syntaxTM n z (by omega) hr
    refine ⟨syntaxTM.liftCfg n c,z.length+2,le_refl _,h,hh,hc,hp,?_,ho⟩
    funext i
    exact reg_zero_init_bumped.eq_regT
  have hcast : ∀ (m : Nat) (he : 0+n = m),
      ((he ▸ syntaxTM.liftTM n) : TM m).HoareTime
        (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
          work = (fun _ => Tape.init []) ∧ out = Tape.init [])
        (guardPre m z (CNF.decode? z).isSome) (z.length+2) := by
    intro m he
    cases he
    exact hbase
  exact hcast n (Nat.zero_add n)

def rejectTM (n : Nat) : TM n where
  Q := Unit
  qstart := ()
  qhalt := ()
  δ := fun _ i w o => allReadBack () i w o
  δ_right_of_start := fun _ i w o => rightOfStart_allIdle i w o

def validBranch (tm : TM n) : TM n := seqTM (guardPrepareTM n) (startedTM tm)
def guardedTM (tm : TM n) : TM n := ifTM (syntaxCheckTM n) (validBranch tm) (rejectTM n)

def Answer (z : List Bool) (out : Tape) : Prop :=
  (z ∈ SAT.language → out.cells 1 = Γ.one) ∧ (z ∉ SAT.language → out.cells 1 = Γ.zero)

theorem guard_transition (z : List Bool) (b : Bool) (inp : Tape) (work : Fin n → Tape)
    (out : Tape) (h : guardPre n z b inp work out) :
    guardPre n z b (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ := by
  rcases h with ⟨hc,hh,rfl,rfl⟩
  have hp : Parked inp := ⟨by omega,by rw [hc]; exact Tape.init_ofBool_cells_ne_start z⟩
  exact ⟨by rw [hp.transitionInput_eq_self]; exact hc,
    by rw [hp.transitionInput_eq_self]; exact hh,
    funext (fun _ => (parked_regTape 0).transitionTape_eq_self),rfl⟩

theorem guarded_correct (tm : TM n) (hne : tm.qstart ≠ tm.qhalt) (T : Nat → Nat)
    (hvalid : ∀ φ : CNF, ∃ c t, t ≤ T φ.encode.length ∧ tm.reachesIn t (tm.initCfg φ.encode) c ∧
      tm.halted c ∧ (φ.Satisfiable → c.output.cells 1 = Γ.one) ∧
      (¬ φ.Satisfiable → c.output.cells 1 = Γ.zero)) :
    (guardedTM tm).DecidesInTime SAT.language (fun L => T L+2*L+14) := by
  intro z
  have hthen : (validBranch tm).HoareTime
      (fun inp work out => guardPre n z true inp work out ∧ (CNF.decode? z).isSome = true)
      (fun _ _ out => Answer z out ∧ out.StartInvariant) (z.length+6+T z.length) := by
    rintro inp work out ⟨hpre,hyes⟩
    cases hd : CNF.decode? z with
    | none => simp [hd] at hyes
    | some φ =>
      have hz := CNF.decode?_sound hd
      subst z
      have hh : ∃ c t, t ≤ T φ.encode.length ∧ tm.reachesIn t (tm.initCfg φ.encode) c ∧
          tm.halted c ∧ Answer φ.encode c.output := by
        obtain ⟨c,t,ht,hr,hh,hy,hn⟩ := hvalid φ
        have he := libraryCNF_decode_language (CNF.decode?_encode φ)
        exact ⟨c,t,ht,hr,hh,fun h => hy (he.mp h),fun h => hn (fun hs => h (he.mpr hs))⟩
      have hstart := started_from_run tm hne φ.encode (T φ.encode.length) (Answer φ.encode) hh
      have h := seqTM_hoareTime _ _ (guard_prepare_correct n φ.encode true)
        (emitPred_transition (parked_init_input φ.encode) (fun _ => parked_regTape 0) []) hstart
      exact h.mono_bound (by omega) inp work out hpre
  have helse : (rejectTM n).HoareTime
      (fun inp work out => guardPre n z false inp work out ∧ (CNF.decode? z).isSome = false)
      (fun _ _ out => Answer z out ∧ out.StartInvariant) 0 := by
    rintro inp work out ⟨hpre,hno⟩
    have hn : z ∉ SAT.language := by
      rintro ⟨φ,hz,_⟩
      rw [hz,CNF.decode?_encode] at hno
      contradiction
    refine ⟨⟨(),inp,work,out⟩,0,le_refl _,.zero,rfl,?_,?_⟩
    · exact ⟨fun h => (hn h).elim,fun _ => by rw [hpre.2.2.2]; rfl⟩
    · rw [hpre.2.2.2]
      exact syntaxVerdict_startInvariant false
  have hwf : ∀ inp work out, guardPre n z (CNF.decode? z).isSome inp work out →
      AllTapesWF inp work out := by
    rintro inp work out ⟨hc,_,rfl,rfl⟩
    exact ⟨by rw [hc]; rfl,by rw [hc]; exact Tape.init_ofBool_cells_ne_start z,
      fun _ => rfl,fun _ => (parked_regTape 0).2,
      (syntaxVerdict_startInvariant _).1,(syntaxVerdict_startInvariant _).2⟩
  have hhead : ∀ inp work out, guardPre n z (CNF.decode? z).isSome inp work out → out.head ≤ 1 := by
    rintro inp work out ⟨_,_,_,rfl⟩
    exact le_refl _
  have hyes : ∀ inp work out, guardPre n z (CNF.decode? z).isSome inp work out → out.cells 1 = Γ.one →
      guardPre n z true (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ ∧
        (CNF.decode? z).isSome = true := by
    intro inp work out h hv
    rw [h.2.2.2,syntaxVerdict_cell] at hv
    have hb : (CNF.decode? z).isSome = true := by
      cases hq : (CNF.decode? z).isSome <;> simp_all [Γ.ofBool]
    exact ⟨hb ▸ guard_transition z _ inp work out h,hb⟩
  have hno : ∀ inp work out, guardPre n z (CNF.decode? z).isSome inp work out → out.cells 1 ≠ Γ.one →
      guardPre n z false (transitionInput inp) (fun i => transitionTape (work i)) ⟨1,out.cells⟩ ∧
        (CNF.decode? z).isSome = false := by
    intro inp work out h hv
    rw [h.2.2.2,syntaxVerdict_cell] at hv
    have hb : (CNF.decode? z).isSome = false := by
      cases hq : (CNF.decode? z).isSome <;> simp_all [Γ.ofBool]
    exact ⟨hb ▸ guard_transition z _ inp work out h,hb⟩
  have hpost : ∀ (inp : Tape) (work : Fin n → Tape) (out : Tape),
      Answer z out ∧ out.StartInvariant → Answer z (transitionTape out) := by
    rintro inp work out ⟨ha,hi⟩
    exact ⟨fun h => by rw [transitionTape_cells out hi.2]; exact ha.1 h,
      fun h => by rw [transitionTape_cells out hi.2]; exact ha.2 h⟩
  have h := ifTM_hoareTime (syntaxCheckTM n) (validBranch tm) (rejectTM n)
    (post := fun _ _ out => Answer z out) (syntax_check_correct n z) hwf hhead hyes hno hthen helse
      hpost hpost
  obtain ⟨c,t,ht,hr,hh,hy,hn⟩ := h _ _ _ ⟨rfl,rfl,rfl⟩
  change t ≤ (z.length+2)+1+max (z.length+6+T z.length) 0+5 at ht
  simp only [Nat.max_zero] at ht
  exact ⟨c,t,by change t ≤ T z.length+2*z.length+14; omega,hr,hh,hy,hn⟩

end IrrRAFEnumeration.SyntaxGuard

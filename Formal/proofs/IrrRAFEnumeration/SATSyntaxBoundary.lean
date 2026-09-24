import proofs.IrrRAFEnumeration.SATSyntaxMachine
import proofs.Complexitylib.Models.TuringMachine.Registers.Emit
import proofs.Complexitylib.Models.TuringMachine.Lift

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

theorem syntaxTM_scan_boundary (bits : List Bool) (q : SyntaxBitState) (inp : Tape)
    (hin : inp.HasBinarySuffix bits) :
    ∃ c, syntaxTM.reachesIn (bits.length+1) (syntaxScanCfg q inp) c ∧
      syntaxTM.halted c ∧ c.input.cells = inp.cells ∧
      c.input.head = inp.head+bits.length ∧
      c.output = syntaxVerdict (syntaxBits q bits) := by
  induction bits generalizing q inp with
  | nil =>
    exact ⟨_,.step (syntaxTM_end_step q inp hin.read_nil) .zero,rfl,rfl,
      (Nat.add_zero _).symm,rfl⟩
  | cons b bs ih =>
    obtain ⟨c,hr,hh,hc,hp,ho⟩ := ih (syntaxBitStep q b) (inp.move .right) hin.move_right_cons
    refine ⟨c,.step (syntaxTM_bit_step q inp b hin.read_cons) hr,hh,hc,?_,ho⟩
    simpa only [Tape.move,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hp

theorem syntaxTM_initial_boundary (z : List Bool) :
    ∃ c, syntaxTM.reachesIn (z.length+2) (syntaxTM.initCfg z) c ∧
      syntaxTM.halted c ∧ c.input.cells = (Tape.init (z.map Γ.ofBool)).cells ∧
      c.input.head = z.length+1 ∧ c.output = syntaxVerdict (CNF.decode? z).isSome := by
  obtain ⟨c,hr,hh,hc,hp,ho⟩ := syntaxTM_scan_boundary z syntaxInitial _
    (Tape.init_move_right_hasBinarySuffix z)
  refine ⟨c,.step (syntaxTM_init_step z) hr,hh,hc,?_,?_⟩
  · simpa only [Tape.move,Tape.init,Nat.zero_add,Nat.add_comm] using hp
  · simpa only [syntaxInitial,syntaxBits_eq_decode] using ho

def syntaxTestTM : TM 4 := syntaxTM.liftTM 4

def syntaxPost (z : List Bool) (inp : Tape) (work : Fin 4 → Tape) (out : Tape) : Prop :=
  inp.cells = (Tape.init (z.map Γ.ofBool)).cells ∧ inp.head = z.length+1 ∧
    work = (fun _ => regTape 0) ∧ out = syntaxVerdict (CNF.decode? z).isSome

theorem syntaxTestTM_correct (z : List Bool) :
    syntaxTestTM.HoareTime
      (fun inp work out => inp = Tape.init (z.map Γ.ofBool) ∧
        work = (fun _ => Tape.init []) ∧ out = Tape.init [])
      (syntaxPost z) (z.length+2) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨c,hr,hh,hc,hp,ho⟩ := syntaxTM_initial_boundary z
  have h := liftTM_reachesIn_initCfg_of_pos syntaxTM 4 z (by omega) hr
  refine ⟨syntaxTM.liftCfg 4 c,z.length+2,le_refl _,h,hh,hc,hp,?_,ho⟩
  funext i
  exact reg_zero_init_bumped.eq_regT

theorem syntaxVerdict_parked (b : Bool) : Parked (syntaxVerdict b) := by
  refine ⟨by rfl,?_⟩
  intro j hj
  cases b <;> simp [syntaxVerdict,syntaxBlankOut,Tape.writeAndMove,Tape.write,Tape.move,
    Tape.init,Function.update,show j ≠ 0 from by omega]
  all_goals split <;> decide

theorem syntaxVerdict_startInvariant (b : Bool) : (syntaxVerdict b).StartInvariant :=
  ⟨by cases b <;> rfl,(syntaxVerdict_parked b).2⟩

end IrrRAFEnumeration.SATSource

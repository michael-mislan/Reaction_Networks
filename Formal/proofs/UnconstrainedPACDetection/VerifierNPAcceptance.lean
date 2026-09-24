import proofs.UnconstrainedPACDetection.VerifierNPMachine

namespace UnconstrainedPACDetection.VerifierNPAcceptance
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open VerifierNPMachine

attribute [local irreducible] VerifierNPStart.machine VerifierNPGuess.machine
  VerifierNPEvaluate.machine
attribute [local irreducible] VerifierNPStart.bound VerifierNPGuess.bound evaluationBudget
attribute [local irreducible] NTM.trace

set_option maxHeartbeats 10000

theorem specified_witness (src wit : List Bool)
    (hlen : wit.length ≤ VerifierNPBound.cap src.length) :
    ∃ choices : Fin (bound src.length) → Bool,
      let d := machine.trace (bound src.length) choices (machine.initCfg src)
      machine.halted d ∧ OutAcc [BinaryIntegerVerifier.verify src wit] d.output := by
  obtain ⟨cg,hg,hbefore⟩ := VerifierNPGuess.generates src wit hlen
  have htail := VerifierNTMSequence.chosen_tail VerifierNPGuess.machine
    VerifierNPEvaluate.machine.toNTM (VerifierNPGuess.bound src.length)
    (evaluationBudget src.length) cg (VerifierNPGuess.initial src)
    (Q := VerifierNPEvaluate.before src wit)
    (R := fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out) hg hbefore
    ((VerifierNPEvaluate.evaluate_hoare src wit).mono_bound
      (evaluation_bound src wit hlen)).toNTM (before_stable src wit)
  have hs := (VerifierNPStart.setup_hoare src).toNTM.strengthen_post
    (fun inp work out h => show inp = word src ∧
        work = VerifierNPPrepare.preparedWork src.length ∧ out = word [] from
      ⟨h.1,h.2.1,h.2.2.eq outAcc_nil_init⟩)
  exact VerifierNTMSequence.prefix_fixed VerifierNPStart.machine.toNTM guessVerify
    (VerifierNPStart.bound src.length) (guessVerifyBound src.length)
    (Tape.init (src.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    (word src) (VerifierNPPrepare.preparedWork src.length) (word [])
    (P := VerifierNPStart.initial src)
    (R := fun _ _ out => OutAcc [BinaryIntegerVerifier.verify src wit] out)
    ⟨rfl,rfl,rfl⟩ hs
    (transitionInput_eq_self (word_parked src).read_ne_start)
    (funext (fun j => transitionTape_eq_self
      (VerifierNPPrepare.prepared_parked src.length j).read_ne_start))
    (transitionTape_eq_self (word_parked []).read_ne_start) htail

theorem verdict_cell (b : Bool) (out : Tape) (h : OutAcc [b] out) :
    out.cells 1 = Γ.ofBool b := by
  have hc := h.2.2.1 0 (by simp)
  simpa using hc

theorem verdict_true (b : Bool) (out : Tape) (h : OutAcc [b] out)
    (hc : out.cells 1 = Γ.one) : b = true := by
  have he := (verdict_cell b out h).symm.trans hc
  cases b <;> simp_all [Γ.ofBool]

theorem decides_of_verifier {n : Nat} (M : NTM n) (T C : Nat → Nat)
    (v : List Bool → List Bool → Bool) (L : Language)
    (short : ∀ src, src ∈ L ↔ ∃ wit, wit.length ≤ C src.length ∧ v src wit = true)
    (sound : ∀ src wit, v src wit = true → src ∈ L)
    (halts : M.AllPathsHaltIn T)
    (generates : ∀ src wit, wit.length ≤ C src.length →
      ∃ choices : Fin (T src.length) → Bool,
        let d := M.trace (T src.length) choices (M.initCfg src)
        M.halted d ∧ OutAcc [v src wit] d.output)
    (outputs : ∀ src (choices : Fin (T src.length) → Bool),
      ∃ wit, wit.length ≤ C src.length ∧
        OutAcc [v src wit] (M.trace (T src.length) choices (M.initCfg src)).output) :
    M.DecidesInTime L T := by
  refine ⟨halts,?_⟩
  intro src
  constructor
  · intro h
    obtain ⟨wit,hlen,hv⟩ := (short src).1 h
    obtain ⟨choices,hh,ho⟩ := generates src wit hlen
    refine ⟨choices,hh,?_⟩
    exact (verdict_cell _ _ ho).trans (congrArg Γ.ofBool hv)
  · rintro ⟨choices,_,ho⟩
    obtain ⟨wit,_,hout⟩ := outputs src choices
    have hv := verdict_true _ _ hout ho
    exact sound src wit hv

theorem decides : machine.DecidesInTime BinaryIntegerVerifier.language bound :=
  decides_of_verifier machine bound VerifierNPBound.cap BinaryIntegerVerifier.verify
    BinaryIntegerVerifier.language BinaryIntegerVerifier.language_iff_short_verified
    (fun _ _ h => BinaryIntegerVerifier.verify_sound h) all_paths_halt specified_witness
    (fun src choices => (verification_hoare src _ _ _ ⟨rfl,rfl,rfl⟩ choices).2)

end UnconstrainedPACDetection.VerifierNPAcceptance

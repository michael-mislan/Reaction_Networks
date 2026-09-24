import proofs.IrrRAFEnumeration.DeadlineBoundary
import proofs.IrrRAFEnumeration.PlacedCountPostlude

namespace IrrRAFEnumeration.InitializedCountDecision
open Complexity Complexity.TM HeaderComparison PolynomialClockSetup InitializedDeadline
  DeadlineBoundary PlacedCountPostlude
variable {n : Nat}

def countDecisionTM (tm : TM n) (p : Polynomial Nat) : TM (n+3) :=
  seqTM (initializedTM tm p) (placedPostlude n)

/-- The no-case test starts from a genuine input configuration and includes
clock construction, source simulation, baseline preparation, and reporting.
Its source-output premise applies only to completed source computations. -/
theorem initialized_count_correct (tm : TM n) (hne : tm.qstart ≠ tm.qhalt)
    (p : Polynomial Nat) (x : List Bool) (actual : Nat)
    (hheader : ∀ d u, tm.reachesIn u (tm.initCfg x) d → tm.halted d →
      UnaryPrefix (parkOutput d.output) actual Γ.zero) :
    ∃ c s b, s ≤ 4*(setupTime p x.length+p.eval x.length+2)+6*x.length+26 ∧
      (countDecisionTM tm p).reachesIn s ((countDecisionTM tm p).initCfg x) c ∧
      (countDecisionTM tm p).halted c ∧
      (b = true ↔ ∃ e u, u ≤ p.eval x.length+1 ∧
        tm.reachesIn u (tm.initCfg x) e ∧ tm.halted e) ∧
      c.output.cells 1 = Γ.ofBool (!(b && decide (actual = x.length+2))) := by
  obtain ⟨d,t,s,b,ht,hs,hd,hr,hh,hb,hflag,hcells,hi,hw,ho,hbd⟩ :=
    initialized_boundary tm hne p x
  let a := completedCfg tm p x d t b
  change a.output.cells = d.output.cells at hcells
  have hInv : a.output.StartInvariant := by
    obtain ⟨_,_,ho'⟩ := run_invariants tm hd (Tape.StartInvariant.init_ofBool x)
      (fun _ => Tape.StartInvariant.init_nil) Tape.StartInvariant.init_nil
    exact ⟨by rw [hcells]; exact ho'.1,by rw [hcells]; exact ho'.2⟩
  have hO : b = true → UnaryPrefix (parkOutput a.output) actual Γ.zero := by
    intro htrue
    have hp := hheader d (t+1) hd (hbd.mp htrue)
    simpa only [UnaryPrefix,parkOutput,hcells] using hp
  have hlen : a.work (placeWorkIdx n 0 (0 : Fin 3)) = regTape x.length :=
    completedCfg_length_register tm p x d t b
  obtain ⟨e,u,hu,he,hhalt,hver⟩ := placed_postlude_correct n x.length actual b
    a.input a.output a.work hi hw ho hInv hlen hflag hO
  have hwt : (fun i => transitionTape (a.work i)) = a.work :=
    funext (fun i => (hw i).transitionTape_eq_self)
  dsimp only [a] at hwt he
  have hseq := seqTM_reachesIn_of_reachesIn (initializedTM tm p) (placedPostlude n) hr hh (by
    simpa only [hi.transitionInput_eq_self,hwt,ho.transitionTape_eq_self] using he)
  refine ⟨phase2Wrap (initializedTM tm p) (placedPostlude n) e,s+1+u,b,?_,hseq,
    (phase2Wrap_halted_iff _ _ _).mpr hhalt,hb,hver⟩
  have hhead := TM.output_head_reachesIn_bound (initializedTM tm p) hr
  change a.output.head ≤ 0+s at hhead
  omega

noncomputable def decisionPolynomial (p : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 4*(setupPolynomial p+p+Polynomial.C 2)+Polynomial.C 6*Polynomial.X+Polynomial.C 26

theorem decisionPolynomial_eval (p : Polynomial Nat) (L : Nat) :
    (decisionPolynomial p).eval L = 4*(setupTime p L+p.eval L+2)+6*L+26 := by
  simp only [decisionPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,setupTime_eq_polynomial]

end IrrRAFEnumeration.InitializedCountDecision

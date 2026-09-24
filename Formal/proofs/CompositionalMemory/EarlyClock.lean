import proofs.CompositionalMemory.MembraneClock
import proofs.CompositionalMemory.WordMembraneRates
import proofs.HeritableCompositions.ClockTails

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def modularDivisionRecorded {k : ℕ} (N : ℕ)
    (D : Finset (ModularCountState k)) : Set (StoppedModularState D) :=
  {s | match s with | none => False | some s => 2*(k*N) ≤ s.val.2}

theorem modular_stopped_early_clock {k : ℕ} (γ b : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset (ModularCountState k))
    (hrate : ∀ c ∈ D, c.2 < 2*(k*N) → (∑ i, γ*(c.1 i 2 : ℝ)) ≤ 2*b*((k*N : ℕ) : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (retainedModularModel γ w hγ hw N D).total c ≤ q)
    (A : Set (StoppedModularState D)) (a : ℝ)
    (hA : ∀ c ∈ A, a ≤ retainedModularObservable D (modularMembraneObservable (k*N) (1/5)) 0 c)
    (c : {c : ModularCountState k // c ∈ D}) :
    a*((retainedModularModel γ w hγ hw N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤
      Real.exp ((12*b*((k*N : ℕ) : ℝ)/25)*(t : ℝ))*modularMembraneObservable (k*N) (1/5) c.val := by
  classical
  let W := retainedModularObservable D (modularMembraneObservable (k*N) (1/5)) 0
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some x => exact (Real.exp_pos _).le
  have hgen : ∀ x, (retainedModularModel γ w hγ hw N D).generator W x ≤
      -(-(12*b*((k*N : ℕ) : ℝ)/25))*W x := by
    intro x
    cases x with
    | none => simp [retainedModularModel,FiniteJumpModel.generator,W,retainedModularObservable]
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N)
      · have hh := (retained_modular_generator_le γ w hγ hw N D (modularMembraneObservable (k*N) (1/5)) 0
          (fun _ _ _ _ _ => (Real.exp_pos _).le) x hx).trans
          (modular_early_generator γ b hγ w (k*N) x.val (hrate x.val x.property hx))
        simpa only [neg_neg] using hh
      · have hp : 0 ≤ (12*b*((k*N : ℕ) : ℝ)/25)*modularMembraneObservable (k*N) (1/5) x.val := by
          unfold modularMembraneObservable
          positivity
        simpa [retainedModularModel,FiniteJumpModel.generator,hx,W,retainedModularObservable] using hp
  have hk : -(12*b*((k*N : ℕ) : ℝ)/25) ≤ q := by
    have hp : 0 ≤ 12*b*((k*N : ℕ) : ℝ)/25 := by positivity
    linarith only [hq,hp]
  have hh := uniformized_event_exponential (retainedModularModel γ w hγ hw N D) q t hq hclock
    A W a (-(12*b*((k*N : ℕ) : ℝ)/25)) hW hA hk hgen (some c)
  simpa only [neg_neg] using hh

theorem modular_early_division_tail {k : ℕ} (γ b : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset (ModularCountState k))
    (hrate : ∀ c ∈ D, c.2 < 2*(k*N) → (∑ i, γ*(c.1 i 2 : ℝ)) ≤ 2*b*((k*N : ℕ) : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : b*(t : ℝ) ≤ 2/5)
    (hclock : ∀ c, (retainedModularModel γ w hγ hw N D).total c ≤ q)
    (c : {c : ModularCountState k // c ∈ D}) (hstart : c.val.2=k*N) :
    ((retainedModularModel γ w hγ hw N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (modularDivisionRecorded N D)) (some c) ≤ Real.exp (-((k*N : ℕ) : ℝ)/125) := by
  have hA : ∀ d ∈ modularDivisionRecorded N D, Real.exp (((k*N : ℕ) : ℝ)/5) ≤
      retainedModularObservable D (modularMembraneObservable (k*N) (1/5)) 0 d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      apply Real.exp_le_exp.mpr
      have hm : (2 : ℝ)*((k*N : ℕ) : ℝ) ≤ d.val.2 := by exact_mod_cast hd
      change ((k*N : ℕ) : ℝ)/5 ≤ (1/5)*((d.val.2 : ℝ)-((k*N : ℕ) : ℝ))
      linarith only [hm]
  have h := modular_stopped_early_clock γ b w hw hγ hb N D hrate q t hq hclock
    (modularDivisionRecorded N D) (Real.exp (((k*N : ℕ) : ℝ)/5)) hA c
  have hs : modularMembraneObservable (k*N) (1/5) c.val=1 := by simp [modularMembraneObservable,hstart]
  rw [hs,mul_one] at h
  have hbtime : (12*b*((k*N : ℕ) : ℝ)/25)*(t : ℝ)-((k*N : ℕ) : ℝ)/5 ≤ -((k*N : ℕ) : ℝ)/125 := by
    have hh := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (k*N) : (0 : ℝ) ≤ (k*N : ℕ))
    nlinarith only [hh]
  exact (exponential_probability_cancel _ _ _ h).trans (Real.exp_le_exp.mpr hbtime)

end CompositionalMemory

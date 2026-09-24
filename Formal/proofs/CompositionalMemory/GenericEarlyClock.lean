import proofs.CompositionalMemory.GenericMembraneClock
import proofs.HeritableCompositions.ClockTails

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def generalDivisionRecorded {k d : ℕ} (N : ℕ)
    (D : Finset (GeneralCountState k d)) : Set (Option {s : GeneralCountState k d // s ∈ D}) :=
  {s | match s with | none => False | some s => 2*(k*N) ≤ s.val.2}

theorem general_stopped_early_clock {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (hcoeff : ∀ i j, 0 ≤ coeff i j) (γ b : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset (GeneralCountState k d))
    (hrate : ∀ c ∈ D, c.2 < 2*(k*N) → (∑ i, γ*(c.1 i z : ℝ)) ≤ 2*b*((k*N : ℕ) : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D).total c ≤ q)
    (A : Set (Option {s : GeneralCountState k d // s ∈ D})) (a : ℝ)
    (hA : ∀ c ∈ A, a ≤ retainedReactionObservable D (generalMembraneObservable (k*N) (1/5)) 0 c)
    (c : {c : GeneralCountState k d // c ∈ D}) :
    a*((retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤
      Real.exp ((12*b*((k*N : ℕ) : ℝ)/25)*(t : ℝ))*generalMembraneObservable (k*N) (1/5) c.val := by
  classical
  let W := retainedReactionObservable D (generalMembraneObservable (k*N) (1/5)) 0
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some x => exact (Real.exp_pos _).le
  have hgen : ∀ x, (retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D).generator W x ≤
      -(-(12*b*((k*N : ℕ) : ℝ)/25))*W x := by
    intro x
    cases x with
    | none => simp [retainedReactionModel,FiniteJumpModel.generator,W,retainedReactionObservable]
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N)
      · have hh := (retained_reaction_generator_le (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D (generalMembraneObservable (k*N) (1/5)) 0
          (fun _ _ _ _ _ => (Real.exp_pos _).le) x hx).trans
          (general_early_clock_generator consume produce coeff z γ b hγ w (k*N) x.val (hrate x.val x.property hx))
        simpa only [neg_neg] using hh
      · have hp : 0 ≤ (12*b*((k*N : ℕ) : ℝ)/25)*generalMembraneObservable (k*N) (1/5) x.val := by
          unfold generalMembraneObservable
          positivity
        simpa [retainedReactionModel,FiniteJumpModel.generator,hx,W,retainedReactionObservable] using hp
  have hk : -(12*b*((k*N : ℕ) : ℝ)/25) ≤ q := by
    have hp : 0 ≤ 12*b*((k*N : ℕ) : ℝ)/25 := by positivity
    linarith only [hq,hp]
  have hh := uniformized_event_exponential (retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D) q t hq hclock
    A W a (-(12*b*((k*N : ℕ) : ℝ)/25)) hW hA hk hgen (some c)
  simpa only [neg_neg] using hh

theorem general_early_division_tail {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (hcoeff : ∀ i j, 0 ≤ coeff i j) (γ b : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset (GeneralCountState k d))
    (hrate : ∀ c ∈ D, c.2 < 2*(k*N) → (∑ i, γ*(c.1 i z : ℝ)) ≤ 2*b*((k*N : ℕ) : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : b*(t : ℝ) ≤ 2/5)
    (hclock : ∀ c, (retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D).total c ≤ q)
    (c : {c : GeneralCountState k d // c ∈ D}) (hstart : c.val.2=k*N) :
    ((retainedReactionModel (generalGlobalNext consume produce z) (generalGlobalRate consume coeff z γ w) (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (generalDivisionRecorded N D)) (some c) ≤ Real.exp (-((k*N : ℕ) : ℝ)/125) := by
  have hA : ∀ d ∈ generalDivisionRecorded N D, Real.exp (((k*N : ℕ) : ℝ)/5) ≤
      retainedReactionObservable D (generalMembraneObservable (k*N) (1/5)) 0 d := by
    intro d hd
    cases d with
    | none => exact False.elim hd
    | some d =>
      apply Real.exp_le_exp.mpr
      have hm : (2 : ℝ)*((k*N : ℕ) : ℝ) ≤ d.val.2 := by exact_mod_cast hd
      change ((k*N : ℕ) : ℝ)/5 ≤ (1/5)*((d.val.2 : ℝ)-((k*N : ℕ) : ℝ))
      linarith only [hm]
  have h := general_stopped_early_clock consume produce coeff z hcoeff γ b w hw hγ hb N D hrate q t hq hclock
    (generalDivisionRecorded N D) (Real.exp (((k*N : ℕ) : ℝ)/5)) hA c
  have hs : generalMembraneObservable (k*N) (1/5) c.val=1 := by simp [generalMembraneObservable,hstart]
  rw [hs,mul_one] at h
  have hbtime : (12*b*((k*N : ℕ) : ℝ)/25)*(t : ℝ)-((k*N : ℕ) : ℝ)/5 ≤ -((k*N : ℕ) : ℝ)/125 := by
    have hh := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (k*N) : (0 : ℝ) ≤ (k*N : ℕ))
    nlinarith only [hh]
  exact (exponential_probability_cancel _ _ _ h).trans (Real.exp_le_exp.mpr hbtime)

end CompositionalMemory

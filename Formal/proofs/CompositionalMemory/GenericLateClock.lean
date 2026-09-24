import proofs.CompositionalMemory.GenericMembraneClock
import proofs.CompositionalMemory.GenericRetainedRecovery
import proofs.HeritableCompositions.ClockTails

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- Late-division tail under the same retained law used for safety and recovery.
Only states still safe and active contribute to the event. -/
theorem general_late_division_tail {k d : ℕ} {ι : Type*} [Fintype ι]
    (consume produce : Fin k → ι → Fin d → ℕ) (coeff : Fin k → ι → ℝ)
    (z : Fin d) (hcoeff : ∀ i j, 0 ≤ coeff i j)
    (γ a : ℝ) (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ)
    (hw : ∀ i j, 0 ≤ w i j) (N : ℕ) (D : Finset (GeneralCountState k d))
    (hrate : ∀ s ∈ D, s.2 < 2*(k*N) → a*((k*N:ℕ):ℝ) ≤ ∑ i, γ*(s.1 i z:ℝ)) :
    let model := retainedReactionModel (generalGlobalNext consume produce z)
      (generalGlobalRate consume coeff z γ w)
      (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw) (fun s => s.2 < 2*(k*N)) D
    ∀ (q t : NNReal) (hq : 0 < (q:ℝ)) (_ : a*(t:ℝ)=11/10)
      (hclock : ∀ s, model.total s ≤ q) (_ : 19*a*((k*N:ℕ):ℝ)/400 ≤ q)
      (s : {s : GeneralCountState k d // s ∈ D}), k*N ≤ s.val.2 →
    (model.uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {x | match x with | none => False | some s => s.val.2 < 2*(k*N)})
      (some s) ≤ Real.exp (-9*((k*N:ℕ):ℝ)/4000) := by
  classical
  intro model q t hq htime hclock hdecay s hstart
  let W := retainedActiveObservable (fun s => s.2 < 2*(k*N)) D (generalMembraneObservable (k*N) (-1/20))
  let event : Set (Option {s : GeneralCountState k d // s ∈ D}) :=
    {x | match x with | none => False | some s => s.val.2 < 2*(k*N)}
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some x =>
      simp only [W,retainedActiveObservable,retainedReactionObservable]
      split_ifs
      · exact (Real.exp_pos _).le
      · exact le_rfl
  have hgen (x) : model.generator W x ≤ -(19*a*((k*N:ℕ):ℝ)/400)*W x := by
    cases x with
    | none => simp [model,W,retainedReactionModel,retainedActiveObservable,retainedReactionObservable,FiniteJumpModel.generator]
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N)
      · have hh := (retained_active_generator_le (generalGlobalNext consume produce z)
          (generalGlobalRate consume coeff z γ w)
          (general_global_rate_nonneg consume coeff z γ w hcoeff hγ hw)
          (fun s => s.2 < 2*(k*N)) D (generalMembraneObservable (k*N) (-1/20))
          (fun _ => (Real.exp_pos _).le) x hx).trans
          (general_late_clock_generator consume produce coeff z γ a hγ w (k*N) x.val
            (hrate x.val x.property hx))
        simpa only [W,retainedActiveObservable,retainedReactionObservable,if_pos hx] using hh
      · simp [model,W,retainedReactionModel,retainedActiveObservable,retainedReactionObservable,
          FiniteJumpModel.generator,hx]
  have hA : ∀ x ∈ event, Real.exp (-((k*N:ℕ):ℝ)/20) ≤ W x := by
    intro x hx
    cases x with
    | none => exact False.elim hx
    | some x =>
      have hxactive : x.val.2 < 2*(k*N) := hx
      have hm : (x.val.2:ℝ) ≤ 2*((k*N:ℕ):ℝ) := by exact_mod_cast hxactive.le
      simp only [W,retainedActiveObservable,retainedReactionObservable,if_pos hxactive]
      apply Real.exp_le_exp.mpr
      change -((k*N:ℕ):ℝ)/20 ≤ (-1/20)*((x.val.2:ℝ)-((k*N:ℕ):ℝ))
      linarith only [hm]
  have hh := uniformized_event_exponential model q t hq hclock event W
    (Real.exp (-((k*N:ℕ):ℝ)/20)) (19*a*((k*N:ℕ):ℝ)/400) hW hA hdecay hgen (some s)
  have hs : W (some s) ≤ 1 := by
    simp only [W,retainedActiveObservable,retainedReactionObservable]
    split_ifs
    · have hm : ((k*N:ℕ):ℝ) ≤ (s.val.2:ℝ) := by exact_mod_cast hstart
      apply Real.exp_le_one_iff.mpr
      change (-1/20)*((s.val.2:ℝ)-((k*N:ℕ):ℝ)) ≤ 0
      linarith only [hm]
    · norm_num
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hs
    (Real.exp_pos (-(19*a*((k*N:ℕ):ℝ)/400)*(t:ℝ))).le)
  rw [mul_one] at hh'
  have heq : -(19*a*((k*N:ℕ):ℝ)/400)*(t:ℝ)-(-((k*N:ℕ):ℝ)/20) = -9*((k*N:ℕ):ℝ)/4000 := by
    calc
      _ = -(19*((k*N:ℕ):ℝ)/400)*(a*(t:ℝ))+((k*N:ℕ):ℝ)/20 := by ring
      _ = _ := by rw [htime]; ring
  simpa only [heq] using exponential_probability_cancel _ _ _ hh'

end CompositionalMemory

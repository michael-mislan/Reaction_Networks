import proofs.CompositionalMemory.MembraneClock
import proofs.HeritableCompositions.ClockTails

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def modularStillLiving {k : ℕ} (D : Finset (ModularCountState k)) :
    Set (StoppedModularState D) := {s | s.isSome}

theorem modular_killed_late_clock {k : ℕ} (γ a : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (N : ℕ) (D : Finset (ModularCountState k))
    (hrate : ∀ s ∈ D, a*((k*N : ℕ) : ℝ) ≤ ∑ i, γ*(s.1 i 2 : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (killedModularModel γ w hγ hw D).total s ≤ q)
    (hdecay : 19*a*((k*N : ℕ) : ℝ)/400 ≤ q)
    (A : Set (StoppedModularState D)) (threshold : ℝ)
    (hA : ∀ s ∈ A, threshold ≤ stoppedModularObservable D (modularMembraneObservable (k*N) (-1/20)) 0 s)
    (s : {s : ModularCountState k // s ∈ D}) :
    threshold*((killedModularModel γ w hγ hw D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some s) ≤
      Real.exp (-(19*a*((k*N : ℕ) : ℝ)/400)*(t : ℝ))*modularMembraneObservable (k*N) (-1/20) s.val := by
  classical
  let W := stoppedModularObservable D (modularMembraneObservable (k*N) (-1/20)) 0
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some x => exact (Real.exp_pos _).le
  have hg (x) : (killedModularModel γ w hγ hw D).generator W x ≤
      -(19*a*((k*N : ℕ) : ℝ)/400)*W x := by
    have h := killed_modular_affine γ w hγ hw D (modularMembraneObservable (k*N) (-1/20))
      (19*a*((k*N : ℕ) : ℝ)/400) 0 (fun _ => (Real.exp_pos _).le) (by positivity) (by norm_num)
      (fun u hu => by simpa only [mul_zero,add_zero] using
        modular_late_generator γ a hγ w (k*N) u (hrate u hu)) x
    simpa only [mul_zero,add_zero] using h
  exact uniformized_event_exponential (killedModularModel γ w hγ hw D) q t hq hclock
    A W threshold (19*a*((k*N : ℕ) : ℝ)/400) hW hA hdecay hg (some s)

theorem modular_late_division_tail {k : ℕ} (γ a : ℝ) (w : Fin k → Fin k → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (N : ℕ) (D : Finset (ModularCountState k)) (hD : ∀ s ∈ D, s.2 < 2*(k*N))
    (hrate : ∀ s ∈ D, a*((k*N : ℕ) : ℝ) ≤ ∑ i, γ*(s.1 i 2 : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ)) (ht : a*(t : ℝ)=11/10)
    (hclock : ∀ s, (killedModularModel γ w hγ hw D).total s ≤ q)
    (hdecay : 19*a*((k*N : ℕ) : ℝ)/400 ≤ q)
    (s : {s : ModularCountState k // s ∈ D}) (hstart : k*N ≤ s.val.2) :
    ((killedModularModel γ w hγ hw D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator (modularStillLiving D)) (some s) ≤
        Real.exp (-9*((k*N : ℕ) : ℝ)/4000) := by
  have hA : ∀ d ∈ modularStillLiving D, Real.exp (-((k*N : ℕ) : ℝ)/20) ≤
      stoppedModularObservable D (modularMembraneObservable (k*N) (-1/20)) 0 d := by
    intro d hd
    cases d with
    | none => simp [modularStillLiving] at hd
    | some d =>
      apply Real.exp_le_exp.mpr
      have hm : (d.val.2 : ℝ) ≤ 2*((k*N : ℕ) : ℝ) := by exact_mod_cast (hD d.val d.property).le
      change -((k*N : ℕ) : ℝ)/20 ≤ (-1/20)*((d.val.2 : ℝ)-((k*N : ℕ) : ℝ))
      linarith only [hm]
  have h := modular_killed_late_clock γ a w hw hγ ha N D hrate q t hq hclock hdecay
    (modularStillLiving D) (Real.exp (-((k*N : ℕ) : ℝ)/20)) hA s
  have hs : modularMembraneObservable (k*N) (-1/20) s.val ≤ 1 := by
    have hm : ((k*N : ℕ) : ℝ) ≤ (s.val.2 : ℝ) := by exact_mod_cast hstart
    change Real.exp ((-1/20)*((s.val.2 : ℝ)-((k*N : ℕ) : ℝ))) ≤ 1
    calc
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith only [hm])
      _ = 1 := Real.exp_zero
  have h' : Real.exp (-((k*N : ℕ) : ℝ)/20)*
      ((killedModularModel γ w hγ hw D).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator (modularStillLiving D)) (some s) ≤
      Real.exp (-(19*a*((k*N : ℕ) : ℝ)/400)*(t : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(19*a*((k*N : ℕ) : ℝ)/400)*(t : ℝ))).le
    exact h.trans (by simpa only [mul_one] using hh)
  have hatime : -(19*a*((k*N : ℕ) : ℝ)/400)*(t : ℝ)-(-((k*N : ℕ) : ℝ)/20) =
      -9*((k*N : ℕ) : ℝ)/4000 := by
    calc
      _ = -(19*((k*N : ℕ) : ℝ)/400)*(a*(t : ℝ))+((k*N : ℕ) : ℝ)/20 := by ring
      _ = _ := by rw [ht]; ring
  simpa only [hatime] using exponential_probability_cancel _ _ _ h'

end CompositionalMemory

import proofs.FiniteCopyReactor.CycleExpectations
import proofs.FiniteCopyReactor.ErrorEnvelope

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def observedPulseCycle (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : PulseOutcome N → BoxCounts V × ReactorCounters → ℝ) : ℝ :=
  ∑ o,pulseMass N p o*jointCycle V r d hV hr hr' hd hd' (f o) (postPulseBox N V p hN o)
    (initialCounters (doseU V p) (doseW V p))

theorem observed_cycle_bounds (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : PulseOutcome N → BoxCounts V × ReactorCounters → ℝ) (C : ℝ)
    (hf : ∀ o X, 0 ≤ f o X ∧ f o X ≤ C) :
    0 ≤ observedPulseCycle N V p hN r d hV hr hr' hd hd' f ∧
      observedPulseCycle N V p hN r d hV hr hr' hd hd' f ≤ C := by
  constructor
  · exact Finset.sum_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o) (joint_cycle_bounds V r d hV hr hr' hd hd' (f o) C (hf o) _ _).1)
  · have h := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (joint_cycle_bounds V r d hV hr hr' hd hd' (f o) C (hf o) (postPulseBox N V p hN o)
        (initialCounters (doseU V p) (doseW V p))).2 (pulseMass_nonneg N p o))
    simpa only [← Finset.sum_mul,pulseMass_total,one_mul] using h

theorem observed_cycle_mono (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f g : PulseOutcome N → BoxCounts V × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ o X, 0 ≤ f o X ∧ f o X ≤ C) (hg : ∀ o X, 0 ≤ g o X ∧ g o X ≤ D)
    (hfg : ∀ o X, f o X ≤ g o X) :
    observedPulseCycle N V p hN r d hV hr hr' hd hd' f ≤
      observedPulseCycle N V p hN r d hV hr hr' hd hd' g := by
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left (joint_cycle_mono V r d hV hr hr' hd hd' (f o) (g o) C D (hf o) (hg o) (hfg o) _ _) (pulseMass_nonneg N p o)

theorem pulse_cycle_add (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f g : BoxCounts V × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D) :
    pulseCycle N V p hN r d hV hr hr' hd hd' (fun X => f X+g X)=
      pulseCycle N V p hN r d hV hr hr' hd hd' f+pulseCycle N V p hN r d hV hr hr' hd hd' g := by
  simp only [pulseCycle,joint_cycle_add V r d hV hr hr' hd hd' f g C D hf hg,mul_add,Finset.sum_add_distrib]

theorem pulse_cycle_success_bound (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    1-oneCycleError V ≤ pulseCycle N V p hN r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator {X | CycleSuccess V X}) := by
  let A : Set (BoxCounts V × ReactorCounters) := {X | CycleSuccess V X}
  let B : Set (BoxCounts V × ReactorCounters) := {X | ¬CycleSuccess V X}
  have he : (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=(fun _ => (1:ℝ)) := by
    funext X
    simp only [FiniteKernel.eventIndicator,A,B,Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have h := pulse_cycle_add N V p hN r d hV (by linarith) hr' hd hd'
    (FiniteKernel.eventIndicator A) (FiniteKernel.eventIndicator B) 1 1
    (FiniteKernel.eventIndicator_bounds A) (FiniteKernel.eventIndicator_bounds B)
  rw [he,pulse_cycle_const] at h
  have hf := pulse_cycle_failure_bound N V p hN hlarge r d hV hr hr' hd hd'
  dsimp [A,B] at h
  linarith

end
end FiniteCopyReactor

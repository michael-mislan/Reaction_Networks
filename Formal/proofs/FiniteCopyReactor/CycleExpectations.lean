import proofs.FiniteCopyReactor.PulseCycle

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

theorem marked_poisson_scale {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (t : NNReal) (c : ℝ) (f : α → ℝ → ℝ) (x : α) (z : ℝ) :
    P.poissonized t (fun y w => c*f y w) x z=c*P.poissonized t f x z := by
  unfold MarkedKernel.poissonized
  simp_rw [P.law_scale]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem joint_cycle_bounds (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (C : ℝ) (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C)
    (N : BoxCounts V) (z : ReactorCounters) :
    0 ≤ jointCycle V r d hV hr hr' hd hd' f N z ∧ jointCycle V r d hV hr hr' hd hd' f N z ≤ C :=
  three_stage_bounds _ _ _ _ _ _ _ C (fun X _ => hf X) _ _

theorem joint_cycle_mono (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f g : BoxCounts V × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D)
    (hfg : ∀ X, f X ≤ g X) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' f N z ≤ jointCycle V r d hV hr hr' hd hd' g N z :=
  three_stage_mono _ _ _ _ _ _ _ _ C D (fun X _ => hf X) (fun X _ => hg X) (fun X _ => hfg X) _ _

theorem joint_cycle_scale (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (c : ℝ) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' (fun X => c*f X) N z=c*jointCycle V r d hV hr hr' hd hd' f N z := by
  unfold jointCycle threeStage
  simp_rw [marked_poisson_scale]

theorem joint_cycle_add (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f g : BoxCounts V × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D)
    (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' (fun X => f X+g X) N z=
      jointCycle V r d hV hr hr' hd hd' f N z+jointCycle V r d hV hr hr' hd hd' g N z :=
  three_stage_add _ _ _ _ _ _ _ _ C D (fun X _ => hf X) (fun X _ => hg X) _ _

theorem pulse_cycle_bounds (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (C : ℝ) (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) :
    0 ≤ pulseCycle N V p hN r d hV hr hr' hd hd' f ∧ pulseCycle N V p hN r d hV hr hr' hd hd' f ≤ C := by
  constructor
  · exact Finset.sum_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o) (joint_cycle_bounds V r d hV hr hr' hd hd' f C hf _ _).1)
  · have h := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (joint_cycle_bounds V r d hV hr hr' hd hd' f C hf (postPulseBox N V p hN o)
        (initialCounters (doseU V p) (doseW V p))).2 (pulseMass_nonneg N p o))
    simpa only [← Finset.sum_mul,pulseMass_total,one_mul] using h

theorem pulse_cycle_const (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (c : ℝ) :
    pulseCycle N V p hN r d hV hr hr' hd hd' (fun _ => c)=c := by
  simp only [pulseCycle,joint_cycle_const,← Finset.sum_mul,pulseMass_total,one_mul]

theorem pulse_cycle_scale (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (c : ℝ) :
    pulseCycle N V p hN r d hV hr hr' hd hd' (fun X => c*f X)=c*pulseCycle N V p hN r d hV hr hr' hd hd' f := by
  simp only [pulseCycle,joint_cycle_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem pulse_cycle_mono (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f g : BoxCounts V × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D) (hfg : ∀ X, f X ≤ g X) :
    pulseCycle N V p hN r d hV hr hr' hd hd' f ≤ pulseCycle N V p hN r d hV hr hr' hd hd' g := by
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left (joint_cycle_mono V r d hV hr hr' hd hd' f g C D hf hg hfg _ _) (pulseMass_nonneg N p o)

end
end FiniteCopyReactor

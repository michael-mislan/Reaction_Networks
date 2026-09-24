import proofs.FiniteReservoir.PulseCycle
import proofs.FiniteCopyReactor.CycleExpectations

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

theorem joint_cycle_bounds (V M : ℕ) (params : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ) (C : ℝ) (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C)
    (N : BoxState V M) (z : ReactorCounters) :
    0 ≤ jointCycle V M params hV f N z ∧ jointCycle V M params hV f N z ≤ C :=
  three_stage_bounds _ _ _ _ _ _ _ C (fun X _ => hf X) _ _

theorem joint_cycle_mono (V M : ℕ) (params : Parameters M) (hV : 0 < (V:ℝ))
    
    (f g : BoxState V M × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D)
    (hfg : ∀ X, f X ≤ g X) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M params hV f N z ≤ jointCycle V M params hV g N z :=
  three_stage_mono _ _ _ _ _ _ _ _ C D (fun X _ => hf X) (fun X _ => hg X) (fun X _ => hfg X) _ _

theorem joint_cycle_scale (V M : ℕ) (params : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ) (c : ℝ) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M params hV (fun X => c*f X) N z=c*jointCycle V M params hV f N z := by
  unfold jointCycle threeStage
  simp_rw [marked_poisson_scale]

theorem joint_cycle_add (V M : ℕ) (params : Parameters M) (hV : 0 < (V:ℝ))
    
    (f g : BoxState V M × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D)
    (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M params hV (fun X => f X+g X) N z=
      jointCycle V M params hV f N z+jointCycle V M params hV g N z :=
  three_stage_add _ _ _ _ _ _ _ _ C D (fun X _ => hf X) (fun X _ => hg X) _ _

theorem pulse_cycle_bounds (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) 
    (f : BoxState V M × ReactorCounters → ℝ) (C : ℝ) (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) :
    0 ≤ pulseCycle N V M p hN params fuel hV f ∧ pulseCycle N V M p hN params fuel hV f ≤ C := by
  constructor
  · exact Finset.sum_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o) (joint_cycle_bounds V M params hV f C hf _ _).1)
  · have h := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (joint_cycle_bounds V M params hV f C hf (postPulse N V M p hN fuel o)
        (initialCounters (doseU V p) (doseW V p))).2 (pulseMass_nonneg N p o))
    simpa only [← Finset.sum_mul,pulseMass_total,one_mul] using h

theorem pulse_cycle_const (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))  (c : ℝ) :
    pulseCycle N V M p hN params fuel hV (fun _ => c)=c := by
  simp only [pulseCycle,joint_cycle_const,← Finset.sum_mul,pulseMass_total,one_mul]

theorem pulse_cycle_scale (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) 
    (f : BoxState V M × ReactorCounters → ℝ) (c : ℝ) :
    pulseCycle N V M p hN params fuel hV (fun X => c*f X)=c*pulseCycle N V M p hN params fuel hV f := by
  simp only [pulseCycle,joint_cycle_scale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem pulse_cycle_mono (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) 
    (f g : BoxState V M × ReactorCounters → ℝ) (C D : ℝ)
    (hf : ∀ X, 0 ≤ f X ∧ f X ≤ C) (hg : ∀ X, 0 ≤ g X ∧ g X ≤ D) (hfg : ∀ X, f X ≤ g X) :
    pulseCycle N V M p hN params fuel hV f ≤ pulseCycle N V M p hN params fuel hV g := by
  apply Finset.sum_le_sum
  intro o _
  exact mul_le_mul_of_nonneg_left (joint_cycle_mono V M params hV f g C D hf hg hfg _ _) (pulseMass_nonneg N p o)

end
end FiniteReservoir

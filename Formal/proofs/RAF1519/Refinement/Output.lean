import proofs.RAF1519.Refinement.Return
import proofs.RAF1519.Refinement.Phase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace RAF1519.Refinement
noncomputable section
open Set MeasureTheory

def outputI (X : ℝ → State) : ℝ := ∫ t in (3:ℝ)..4, ProductiveRecovery.inventory (free (X t))
def outputX (X : ℝ → State) : ℝ := ∫ t in (3:ℝ)..4, X t 2
def totalService (d theta : ℝ) (X : ℝ → State) : ℝ := ∫ t in (0:ℝ)..4, service d (1/100) theta (X t)
def foodU (p : Intervention) : ℝ := 5-p.q+p.eU
def foodW (p : Intervention) : ℝ := 5-p.q+p.eW

theorem food_bounds (p : Intervention) : foodU p ≤ 951/200 ∧ foodW p ≤ 951/200 := by
  dsimp [foodU,foodW]
  constructor <;> linarith [p.q_lower,p.eU_upper,p.eW_upper]

theorem deterministic_service_rate (d theta : ℝ) (c : State) (ht : 0 < theta)
    (hd' : d ≤ 1/25) (hc : ∀ i, 0 ≤ c i) (hx : c 2 ≤ 11/10)
    (hb : c 6 ≤ (1101/1000)*theta) : service d (1/100) theta c ≤ 112201/2500000 := by
  have hb' : c 6/theta ≤ 1101/1000 := (div_le_iff₀ ht).2 hb
  have hn : 0 ≤ (1+1/100)*c 2+(1/100)*(c 6/theta) :=
    add_nonneg (mul_nonneg (by norm_num) (hc 2))
      (mul_nonneg (by norm_num) (div_nonneg (hc 6) ht.le))
  have hm := mul_le_mul_of_nonneg_right hd' hn
  have hu : (1+1/100)*c 2+(1/100)*(c 6/theta) ≤ 112201/100000 := by linarith
  have he : service d (1/100) theta c =
      d * ((1+1/100)*c 2+(1/100)*(c 6/theta)) := by
    dsimp [service]
    ring
  rw [he]
  linarith

theorem trajectory_output (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (p : Intervention) (c : State) (hc : Ready theta c) (X : ℝ → State)
    (h0 : X 0 = pulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (1/100) theta (X t)) t) :
    1/28 ≤ outputI X ∧ 1/540 ≤ outputX X ∧ totalService d theta X ≤ 112201/625000 := by
  obtain ⟨ha0,hb0⟩ := pulse_material p c hc.1 hc.2.1 hc.2.2.1
  rw [← h0] at ha0 hb0
  have hcor := material_corridor r d (1/100) theta X hX ha0 hb0
  have hret := trajectory_return r d theta hr hr' hd hd' ht ht' p c hc X h0 hn hX
  have hbinit : X 0 6 ≤ (1101/1000)*theta := by
    rw [h0]; exact (pulse_intermediate p c hc.1).trans hc.2.2.2.2
  have hD := intermediate_ceiling r d theta hd ht X hn hX
    (fun t ht0 => (hcor t ht0).1.2) (fun t ht0 => (hcor t ht0).2.2) hbinit
  have hxfloor (t : ℝ) (ht0 : t ∈ Icc (3:ℝ) 4) : 1/540 ≤ X t 2 := by
    have hh := free_phase_floor r d theta hr hr' hd hd' ht X hn hX
      (fun s hs => ⟨(hcor s hs).1.2,(hcor s hs).2.2⟩) (t-1/35) (by linarith [ht0.1])
    rw [sub_add_cancel] at hh
    linarith [hret.1 (t-1/35) (by linarith [ht0.1])]
  have hifloor (t : ℝ) (ht0 : t ∈ Icc (3:ℝ) 4) : 1/28 ≤ ProductiveRecovery.inventory (free (X t)) := by
    have hh := ProductiveRecovery.inventory_lower (free (X t)) (free_nonneg _ (hn t (by linarith [ht0.1])))
    change (5/7)*stock (X t) ≤ _ at hh
    linarith [hret.1 t (by linarith [ht0.1])]
  have hservice (t : ℝ) (ht0 : t ∈ Icc (0:ℝ) 4) : service d (1/100) theta (X t) ≤ 112201/2500000 :=
    deterministic_service_rate d theta (X t) ht hd' (hn t ht0.1)
      (coordinate_bound _ (hn t ht0.1) (hcor t ht0.1).1.2 (hcor t ht0.1).2.2 2) (hD t ht0.1)
  have hdi (t : ℝ) (ht0 : 0 ≤ t) : DifferentiableAt ℝ (fun s => ProductiveRecovery.inventory (free (X s))) t := by
    have h := hasDerivAt_pi.1 (hX t ht0)
    exact ((((h 2).add (h 3)).add (h 4)).add ((h 5).const_mul 2)).differentiableAt
  have hds (t : ℝ) (ht0 : 0 ≤ t) : DifferentiableAt ℝ (fun s => service d (1/100) theta (X s)) t := by
    have h := hasDerivAt_pi.1 (hX t ht0)
    exact (((h 2).const_mul (d*(1+1/100))).add ((h 6).const_mul (d*(1/100)/theta))).differentiableAt
  have hi : IntervalIntegrable (fun t => ProductiveRecovery.inventory (free (X t))) volume 3 4 :=
    (show ContinuousOn _ (Icc (3:ℝ) 4) from fun t ht0 =>
      (hdi t (by linarith [ht0.1])).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have hx : IntervalIntegrable (fun t => X t 2) volume 3 4 :=
    (show ContinuousOn _ (Icc (3:ℝ) 4) from fun t ht0 =>
      (hasDerivAt_pi.1 (hX t (by linarith [ht0.1])) 2).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have hs : IntervalIntegrable (fun t => service d (1/100) theta (X t)) volume 0 4 :=
    (show ContinuousOn _ (Icc (0:ℝ) 4) from fun t ht0 =>
      (hds t ht0.1).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have hI := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/28:ℝ)) volume 3 4) hi hifloor
  have hXout := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/540:ℝ)) volume 3 4) hx hxfloor
  have hS := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num) hs
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (112201/2500000:ℝ)) volume 0 4) hservice
  norm_num at hI hXout hS
  exact ⟨hI,hXout,hS⟩
end
end RAF1519.Refinement

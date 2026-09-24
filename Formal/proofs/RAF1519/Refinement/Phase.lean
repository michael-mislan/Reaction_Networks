import proofs.RAF1519.Refinement.FlowBounds
import proofs.ProductiveRecovery.PhaseTransfer

namespace RAF1519.Refinement
noncomputable section

theorem phase_comparison (r d theta : ℝ) (c : State) (hc : ∀ i, 0 ≤ c i)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta)
    (hA : materialA c ≤ 11/10) (hB : materialB c ≤ 11/10) :
    -70*c 2+20*c 3+38*c 5 ≤ field r d (1/100) theta c 2 ∧
    -70*c 3+20*c 4 ≤ field r d (1/100) theta c 3 ∧
    -70*c 4 ≤ field r d (1/100) theta c 4 ∧
    -70*c 5+20*c 4 ≤ field r d (1/100) theta c 5 := by
  have hb := coordinate_bound c hc hA hB
  have hux := mul_le_mul_of_nonneg_right (hb 0) (hc 2)
  have hwc := mul_le_mul_of_nonneg_right (hb 1) (hc 3)
  have hxx := mul_le_mul_of_nonneg_right (hb 2) (hc 2)
  have hrx := mul_le_mul_of_nonneg_right hr' (sq_nonneg (c 2))
  have hrl := mul_le_mul_of_nonneg_right hr (hc 5)
  have hrz := mul_le_mul_of_nonneg_right hr' (hc 5)
  have hdx := mul_le_mul_of_nonneg_right hd' (hc 2)
  have him : 0 ≤ (1/500000000:ℝ)*c 0*c 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (hc 0)) (hc 1)
  have hxu := mul_nonneg (hc 2) (hc 0)
  have hcw := mul_nonneg (hc 3) (hc 1)
  have hrxx := mul_nonneg (show 0 ≤ r by linarith) (sq_nonneg (c 2))
  have hret : 0 ≤ d*(1/100)/theta*c 6 :=
    mul_nonneg (div_nonneg (mul_nonneg hd (by norm_num)) ht.le) (hc 6)
  simp [field,firstFlux,ProductiveRecovery.flux,free]
  constructor
  · nlinarith [hc 2]
  constructor
  · nlinarith [hc 3]
  constructor <;> nlinarith [hc 4,hc 5]

theorem deriv_free (X : ℝ → State) (v : State) (t : ℝ) (h : HasDerivAt X v t) :
    HasDerivAt (fun s => free (X s)) (free v) t := by
  apply hasDerivAt_pi.2
  intro i
  fin_cases i <;> exact hasDerivAt_pi.1 h _

theorem free_phase_floor (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (htheta : 0 < theta) (X : ℝ → State)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (1/100) theta (X t)) t)
    (hcor : ∀ t, 0 ≤ t → materialA (X t) ≤ 11/10 ∧ materialB (X t) ≤ 11/10)
    (t : ℝ) (ht : 0 ≤ t) : (1/27)*stock (X t) ≤ X (t+1/35) 2 := by
  let Z : ℝ → ProductiveRecovery.State := fun s => free (X (t+s))
  let W : ℝ → ProductiveRecovery.State := fun s => free (field r d (1/100) theta (X (t+s)))
  have hZ (s : ℝ) (hs : 0 ≤ s) : HasDerivAt Z (W s) s := by
    have hshift : HasDerivAt (fun v : ℝ => t+v) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add t
    have hh := deriv_free X _ (t+s) (hX (t+s) (by linarith))
    simpa [Z,W] using hh.scomp s hshift
  have hp := ProductiveRecovery.phase_transfer Z W hZ
    (fun s hs => phase_comparison r d theta (X (t+s)) (hn (t+s) (by linarith))
      hr hr' hd hd' htheta (hcor (t+s) (by linarith)).1 (hcor (t+s) (by linarith)).2)
    (1/35) (by norm_num)
  have he : Real.exp 2 < 9 := by
    have hh := Real.exp_one_lt_three
    have heq : Real.exp 2 = Real.exp 1*Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [heq]
    nlinarith [Real.exp_pos 1]
  have hcoef : (116/343)*stock (X t) ≤
      X t 2+20*(1/35)*X t 3+580*(1/35)^2*X t 4+38*(1/35)*X t 5 := by
    simp [stock,ProductiveRecovery.Y,free]
    linarith [(hn t ht) 2,(hn t ht) 3,(hn t ht) 5]
  norm_num [Z,free] at hp
  change X t 2+(4/7)*X t 3+(116/245)*X t 4+(38/35)*X t 5 ≤
    Real.exp 2*X (t+1/35) 2 at hp
  have hx := hn (t+1/35) (by linarith) 2
  have hmul := mul_le_mul_of_nonneg_right he.le hx
  have hy : 0 ≤ stock (X t) := by
    simp [stock,ProductiveRecovery.Y,free]
    linarith [(hn t ht) 2,(hn t ht) 3,(hn t ht) 4,(hn t ht) 5]
  nlinarith
end
end RAF1519.Refinement

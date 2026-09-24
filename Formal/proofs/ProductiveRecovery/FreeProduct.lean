import proofs.ProductiveRecovery.PhaseTransfer
import proofs.ProductiveRecovery.StrongOutput

namespace ProductiveRecovery
noncomputable section
open MeasureTheory Set

theorem free_phase_floor (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (X : ℝ → State)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hcor : ∀ t, 0 ≤ t → A (X t) ≤ 11/10 ∧ B (X t) ≤ 11/10)
    (t : ℝ) (ht : 0 ≤ t) : (1/27)*Y (X t) ≤ X (t+1/35) 2 := by
  let Z : ℝ → State := fun s => X (t+s)
  have hZ (s : ℝ) (hs : 0 ≤ s) : HasDerivAt Z (field r d (Z s)) s := by
    have hshift : HasDerivAt (fun v : ℝ => t+v) 1 s := by
      simpa only [id_eq] using (hasDerivAt_id s).const_add t
    simpa [Z] using (hX (t+s) (by linarith)).scomp s hshift
  have hp := phase_transfer Z (fun s => field r d (Z s)) hZ
    (fun s hs => phase_comparison r d (Z s) (hn (t+s) (by linarith)) hr hr' hd hd'
      (hcor (t+s) (by linarith)).1 (hcor (t+s) (by linarith)).2) (1/35) (by norm_num)
  have he : Real.exp 2 < 9 := by
    have hh := Real.exp_one_lt_three
    have heq : Real.exp 2 = Real.exp 1*Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [heq]
    nlinarith [Real.exp_pos 1]
  have hcoef : (116/343)*Y (X t) ≤
      X t 2+20*(1/35)*X t 3+580*(1/35)^2*X t 4+38*(1/35)*X t 5 := by
    dsimp [Y]
    linarith [(hn t ht) 2,(hn t ht) 3,(hn t ht) 5]
  norm_num [Z] at hp
  have hx := (hn (t+1/35) (by linarith)) 2
  have hmul := mul_le_mul_of_nonneg_right he.le hx
  have hy : 0 ≤ Y (X t) := by
    dsimp [Y]
    linarith [(hn t ht) 2,(hn t ht) 3,(hn t ht) 4,(hn t ht) 5]
  nlinarith

theorem routine_free_export (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c)
    (X : ℝ → State) (h0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    (∀ t ∈ Icc (3:ℝ) 4, 1/540 ≤ X t 2) ∧
      1/540 ≤ ∫ t in (3:ℝ)..4, X t 2 := by
  have hcor := (trajectory_return r d hr hr' hd hd' p c (strong_admitted c hc) X h0 hn hX).1
  have hY := (routine_return r d hr hr' hd hd' p c hc X h0 hn hX).1
  have hfloor (t : ℝ) (ht : t ∈ Icc (3:ℝ) 4) : 1/540 ≤ X t 2 := by
    have h := free_phase_floor r d hr hr' hd hd' X hn hX
      (fun s hs => ⟨(hcor s hs).1.2,(hcor s hs).2.2⟩) (t-1/35) (by linarith [ht.1])
    rw [sub_add_cancel] at h
    linarith [hY (t-1/35) (by linarith [ht.1])]
  refine ⟨hfloor,?_⟩
  have hi : IntervalIntegrable (fun t => X t 2) volume 3 4 :=
    (show ContinuousOn (fun t => X t 2) (Icc (3:ℝ) 4) from
      fun t ht => (hasDerivAt_pi.1 (hX t (by linarith [ht.1])) 2).continuousAt.continuousWithinAt).intervalIntegrable_of_Icc (by norm_num)
  have h := intervalIntegral.integral_mono_on (a := (3:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/540:ℝ)) volume 3 4) hi hfloor
  norm_num at h
  exact h

end
end ProductiveRecovery

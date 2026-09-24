import proofs.ProductiveRecovery.ProductiveReturn

namespace ProductiveRecovery
noncomputable section
open Set

theorem corridor_norm (c : State) (hn : Nonneg c) (ha : A c ≤ 11/10) (hb : B c ≤ 11/10) :
    ‖c‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).2
  intro i
  rw [Real.norm_eq_abs,abs_of_nonneg (hn i)]
  dsimp [A,B] at ha hb
  fin_cases i
  · change c 0 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  · change c 1 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  · change c 2 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  · change c 3 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  · change c 4 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]
  · change c 5 ≤ 2
    linarith [hn 0,hn 1,hn 2,hn 3,hn 4,hn 5]

theorem bounded_source_unique (r d : ℝ) (X Z : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (field r d (Z t)) t)
    (h0 : X 0 = Z 0)
    (hxb : ∀ t, 0 ≤ t → ‖X t‖ ≤ 2) (hzb : ∀ t, 0 ≤ t → ‖Z t‖ ≤ 2) :
    ∀ t, 0 ≤ t → X t = Z t := by
  obtain ⟨K,hK⟩ := (field_contDiff r d).contDiffOn.exists_lipschitzOnWith
    (s := Metric.closedBall (0:State) 2) (by norm_num)
    (convex_closedBall (0:State) 2) (isCompact_closedBall (0:State) 2)
  intro t ht
  have h := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => field r d) (s := fun _ => Metric.closedBall (0:State) 2)
    (a := 0) (b := t) (K := K) (f := X) (g := Z)
    (fun _ _ => hK)
    (fun s hs => (hX s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hX s hs.1).hasDerivWithinAt)
    (fun s hs => by simpa [Metric.mem_closedBall,dist_zero_right] using hxb s hs.1)
    (fun s hs => (hZ s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hZ s hs.1).hasDerivWithinAt)
    (fun s hs => by simpa [Metric.mem_closedBall,dist_zero_right] using hzb s hs.1) h0
  exact h ⟨ht,le_rfl⟩

theorem actual_return_unique (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c)
    (X Z : ℝ → State) (hX0 : X 0 = pulse p c) (hZ0 : Z 0 = pulse p c)
    (hnX : ∀ t, 0 ≤ t → Nonneg (X t)) (hnZ : ∀ t, 0 ≤ t → Nonneg (Z t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (field r d (Z t)) t) :
    ∀ t, 0 ≤ t → X t = Z t := by
  have hxcor := (trajectory_return r d hr hr' hd hd' p c hc X hX0 hnX hX).1
  have hzcor := (trajectory_return r d hr hr' hd hd' p c hc Z hZ0 hnZ hZ).1
  exact bounded_source_unique r d X Z hX hZ (hX0.trans hZ0.symm)
    (fun t ht => corridor_norm _ (hnX t ht) (hxcor t ht).1.2 (hxcor t ht).2.2)
    (fun t ht => corridor_norm _ (hnZ t ht) (hzcor t ht).1.2 (hzcor t ht).2.2)

end
end ProductiveRecovery

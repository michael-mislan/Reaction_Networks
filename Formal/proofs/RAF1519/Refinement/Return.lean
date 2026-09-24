import proofs.RAF1519.Refinement.FlowBounds
import proofs.RAF1519.Refinement.Stock
import proofs.ProductiveRecovery.StrongScalar

namespace RAF1519.Refinement
noncomputable section

/-- Recovery follows from the literal seven-coordinate evolution, including retained D. -/
theorem trajectory_return (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (p : Intervention) (c : State) (hc : Ready theta c) (X : ℝ → State)
    (h0 : X 0 = pulse p c) (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (1/100) theta (X t)) t) :
    (∀ t, 5/2 ≤ t → 1/20 ≤ stock (X t)) ∧ (∀ t, 3 ≤ t → Ready theta (X t)) := by
  obtain ⟨ha0,hb0⟩ := pulse_material p c hc.1 hc.2.1 hc.2.2.1
  rw [← h0] at ha0 hb0
  have hcor := material_corridor r d (1/100) theta X hX ha0 hb0
  have hbinit : X 0 6 ≤ (1101/1000)*theta := by
    rw [h0]
    exact (pulse_intermediate p c hc.1).trans hc.2.2.2.2
  have hD := intermediate_ceiling r d theta hd ht X hn hX
    (fun t ht => (hcor t ht).1.2) (fun t ht => (hcor t ht).2.2) hbinit
  have hfree := fun t ht0 => free_corridor (X t) theta ht'
    (hcor t ht0).1.1 (hcor t ht0).2.1 (hD t ht0)
  have hy0 : 49/4000 ≤ stock (X 0) := by
    rw [h0]
    exact pulse_stock p c hc.1 hc.2.2.2.1
  have he : (1/20:ℝ)/(49/4000) ≤ Real.exp ((3/5)*(5/2)) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hy := ProductiveRecovery.strong_scheduled_recovery
    (fun t => stock (X t)) (fun t => stock (field r d (1/100) theta (X t)))
    (fun t ht0 => deriv_stock X _ t (hX t ht0)) (49/4000) (5/2)
    (by norm_num) hy0 (by norm_num) he
    (fun t ht0 _ hlow => guarded_growth r d theta (X t) (hn t ht0) hr hr' hd hd' ht.le
      (hfree t ht0).1 (hfree t ht0).2 (by linarith))
  have hmat := material_return r d (1/100) theta X hX ha0 hb0
  refine ⟨hy,?_⟩
  intro t ht3
  have ht0 : 0 ≤ t := by linarith
  exact ⟨hn t ht0,(hmat t ht3).1,(hmat t ht3).2,hy t (by linarith),hD t ht0⟩

theorem exists_returning_cycle (r d theta : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (ht : 0 < theta) (ht' : theta ≤ 1/100)
    (p : Intervention) (c : State) (hc : Ready theta c) :
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (1/100) theta (X t)) t) ∧
      (∀ t, 5/2 ≤ t → 1/20 ≤ stock (X t)) ∧ Ready theta (X 4) := by
  obtain ⟨X,h0,hn,hX⟩ := global_nonnegative_solution r d (1/100) theta
    (by linarith) hd (by norm_num) ht (pulse p c) (pulse_nonnegative p c hc.1)
  have hh := trajectory_return r d theta hr hr' hd hd' ht ht' p c hc X h0 hn hX
  exact ⟨X,h0,hn,hX,hh.1,hh.2 4 (by norm_num)⟩
end
end RAF1519.Refinement

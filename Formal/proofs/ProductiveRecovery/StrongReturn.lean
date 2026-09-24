import proofs.ProductiveRecovery.ProductiveReturn
import proofs.ProductiveRecovery.StrongGrowth
import proofs.ProductiveRecovery.StrongScalar
import proofs.ProductiveRecovery.StrongMaterial

namespace ProductiveRecovery
noncomputable section

def StrongReturned (c : State) : Prop := Nonneg c ∧
  (159/160 ≤ A c ∧ A c ≤ 161/160) ∧
  (159/160 ≤ B c ∧ B c ≤ 161/160) ∧ 1/20 ≤ Y c

theorem strong_admitted (c : State) (h : StrongReturned c) : Admitted c := by
  obtain ⟨hn,ha,hb,hy⟩ := h
  refine ⟨hn,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> linarith [ha.1,ha.2,hb.1,hb.2]

theorem strong_trajectory_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c)
    (X : ℝ → State) (hX0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t)
    (b0 D : ℝ) (hb0 : 0 < b0) (hy0 : b0 ≤ Y (X 0))
    (hD : 0 ≤ D) (he : (1/20)/b0 ≤ Real.exp ((3/5)*D)) :
    (∀ t, D ≤ t → 1/20 ≤ Y (X t)) ∧
    ∀ t, max 3 D ≤ t → StrongReturned (X t) := by
  obtain ⟨hcor,_⟩ := trajectory_return r d hr hr' hd hd' p c hc X hX0 hn hX
  have hy := strong_scheduled_recovery (fun s => Y (X s)) (fun s => Y (field r d (X s)))
    (fun t ht => deriv_Y X _ t (hX t ht)) b0 D hb0 hy0 hD he
    (fun t ht _ hlow => strong_guarded_growth r d (X t) (hn t ht) hr hr' hd hd'
      (hcor t ht).1.1 (hcor t ht).2.1 hlow)
  have hda : ∀ t, 0 ≤ t → HasDerivAt (fun s => A (X s)) (1-A (X t)) t := by
    intro t ht
    simpa only [material_A] using deriv_A X _ t (hX t ht)
  have hdb : ∀ t, 0 ≤ t → HasDerivAt (fun s => B (X s)) (1-B (X t)) t := by
    intro t ht
    simpa only [material_B] using deriv_B X _ t (hX t ht)
  refine ⟨hy,?_⟩
  intro t ht
  have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
  have htD : D ≤ t := (le_max_right _ _).trans ht
  exact ⟨hn t (by linarith),strong_material_interior _ hda (hcor 0 le_rfl).1 t ht3,
    strong_material_interior _ hdb (hcor 0 le_rfl).2 t ht3,hy t htD⟩

theorem conditioning_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c)
    (X : ℝ → State) (hX0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    ∀ t, 12 ≤ t → StrongReturned (X t) := by
  have hy0 : 49/1000000 ≤ Y (X 0) := by
    rw [hX0]
    have hp := pulse_catalyst p c hc.1
    linarith [hc.2.2.2]
  have he : (1/20:ℝ)/(49/1000000) ≤ Real.exp ((3/5)*12) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 36/5) 10
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have h := (strong_trajectory_return r d hr hr' hd hd' p c hc X hX0 hn hX
    (49/1000000) 12 (by norm_num) hy0 (by norm_num) he).2
  norm_num at h
  exact h

theorem routine_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : StrongReturned c)
    (X : ℝ → State) (hX0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    (∀ t, 5/2 ≤ t → 1/20 ≤ Y (X t)) ∧
    ∀ t, 3 ≤ t → StrongReturned (X t) := by
  have hy0 : 49/4000 ≤ Y (X 0) := by
    rw [hX0]
    have hp := pulse_catalyst p c hc.1
    linarith [hc.2.2.2]
  have he : (1/20:ℝ)/(49/4000) ≤ Real.exp ((3/5)*(5/2)) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2) 4
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have h := strong_trajectory_return r d hr hr' hd hd' p c (strong_admitted c hc) X hX0 hn hX
    (49/4000) (5/2) (by norm_num) hy0 (by norm_num) he
  norm_num at h
  exact h

end
end ProductiveRecovery

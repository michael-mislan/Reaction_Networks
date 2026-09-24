import proofs.ProductiveRecovery.MaterialCoordinates
import proofs.ProductiveRecovery.WeightedGrowth
import proofs.ProductiveRecovery.WithdrawalRefill
import proofs.ProductiveRecovery.ScalarRecovery

namespace ProductiveRecovery
noncomputable section

def Admitted (c : State) : Prop := Nonneg c ∧
  (9/10 ≤ A c ∧ A c ≤ 11/10) ∧ (9/10 ≤ B c ∧ B c ≤ 11/10) ∧ 1/5000 ≤ Y c
def Returned (c : State) : Prop := Nonneg c ∧
  (159/160 ≤ A c ∧ A c ≤ 161/160) ∧
  (159/160 ≤ B c ∧ B c ≤ 161/160) ∧ 1/2500 ≤ Y c

theorem returned_admitted (c : State) (h : Returned c) : Admitted c := by
  obtain ⟨hn,ha,hb,hy⟩ := h
  refine ⟨hn,⟨?_,?_⟩,⟨?_,?_⟩,?_⟩ <;> linarith [ha.1,ha.2,hb.1,hb.2]

theorem trajectory_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c)
    (X : ℝ → State) (hX0 : X 0 = pulse p c)
    (hn : ∀ t, 0 ≤ t → Nonneg (X t))
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) :
    (∀ t, 0 ≤ t → (9/10 ≤ A (X t) ∧ A (X t) ≤ 11/10) ∧
      (9/10 ≤ B (X t) ∧ B (X t) ≤ 11/10)) ∧
    ∀ t, 4 ≤ t → Returned (X t) := by
  obtain ⟨hca,hcb⟩ := pulse_material p c hc.1 hc.2.1 hc.2.2.1
  have ha0 : 9/10 ≤ A (X 0) ∧ A (X 0) ≤ 11/10 := by
    rw [hX0]; constructor <;> linarith [hca.1,hca.2]
  have hb0 : 9/10 ≤ B (X 0) ∧ B (X 0) ≤ 11/10 := by
    rw [hX0]; constructor <;> linarith [hcb.1,hcb.2]
  have hda : ∀ t, 0 ≤ t → HasDerivAt (fun s => A (X s)) (1-A (X t)) t := by
    intro t ht
    simpa only [material_A] using deriv_A X _ t (hX t ht)
  have hdb : ∀ t, 0 ≤ t → HasDerivAt (fun s => B (X s)) (1-B (X t)) t := by
    intro t ht
    simpa only [material_B] using deriv_B X _ t (hX t ht)
  have ha := scalar_material_corridor _ hda ha0
  have hb := scalar_material_corridor _ hdb hb0
  have hy0 : 49/1000000 ≤ Y (X 0) := by
    rw [hX0]
    have h := pulse_catalyst p c hc.1
    linarith [hc.2.2.2]
  have hy := guarded_scheduled_recovery (fun s => Y (X s)) (fun s => Y (field r d (X s)))
    (fun t ht => deriv_Y X _ t (hX t ht)) hy0
    (fun t ht _ hlow => guarded_growth r d (X t) (hn t ht) hr hr' hd hd'
      (ha t ht).1 (hb t ht).1 hlow)
  refine ⟨fun t ht => ⟨ha t ht,hb t ht⟩,?_⟩
  intro t ht
  exact ⟨hn t (by linarith),scalar_material_interior _ hda ha0 t ht,
    scalar_material_interior _ hdb hb0 t ht,hy t ht⟩

theorem exists_actual_return (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (p : Intervention) (c : State) (hc : Admitted c) :
    ∃ X : ℝ → State, X 0 = pulse p c ∧
      (∀ t, 0 ≤ t → Nonneg (X t)) ∧
      (∀ t, 0 ≤ t → HasDerivAt X (field r d (X t)) t) ∧
      (∀ t, 0 ≤ t → (9/10 ≤ A (X t) ∧ A (X t) ≤ 11/10) ∧
        (9/10 ≤ B (X t) ∧ B (X t) ≤ 11/10)) ∧
      ∀ t, 4 ≤ t → Returned (X t) := by
  obtain ⟨X,h0,hn,hX⟩ := global_nonnegative_solution r d (by linarith) hd
    (pulse p c) (pulse_nonnegative p c hc.1)
  obtain ⟨hcor,hret⟩ := trajectory_return r d hr hr' hd hd' p c hc X h0 hn hX
  exact ⟨X,h0,hn,hX,hcor,hret⟩

end
end ProductiveRecovery

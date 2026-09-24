import proofs.RandomViability.BindingResourceFoster

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def resourcePotential (V : ℝ) (N : Counts) : ℝ :=
  upperUnitPotential true V N + lowerUnitPotential true V N +
  upperUnitPotential false V N + lowerUnitPotential false V N

theorem resourcePotential_nonneg (V : ℝ) (N : Counts) :
    0 ≤ resourcePotential V N := by
  unfold resourcePotential upperUnitPotential lowerUnitPotential
  positivity

theorem resourcePotential_exit (V : ℕ) (N : Counts) (h : ¬resourceGood N V) :
    1 ≤ resourcePotential V N := by
  have hu := (Real.exp_pos ((1/100)*(unitObs true N-(11/10)*(V:ℝ)))).le
  have hlu := (Real.exp_pos ((-1/100)*(unitObs true N-(9/10)*(V:ℝ)))).le
  have hw := (Real.exp_pos ((1/100)*(unitObs false N-(11/10)*(V:ℝ)))).le
  have hlw := (Real.exp_pos ((-1/100)*(unitObs false N-(9/10)*(V:ℝ)))).le
  unfold resourceGood at h
  simp only [not_and_or, not_le] at h
  unfold resourcePotential upperUnitPotential lowerUnitPotential
  rcases h with h | h | h | h
  · have he : 1 ≤ Real.exp ((-1/100)*(unitObs true N-(9/10)*(V:ℝ))) :=
      Real.one_le_exp_iff.mpr (by simpa [unitObs] using (show 0 ≤ (-1/100)*(uCount N-(9/10)*(V:ℝ)) by linarith))
    linarith
  · have he : 1 ≤ Real.exp ((1/100)*(unitObs true N-(11/10)*(V:ℝ))) :=
      Real.one_le_exp_iff.mpr (by simpa [unitObs] using (show 0 ≤ (1/100)*(uCount N-(11/10)*(V:ℝ)) by linarith))
    linarith
  · have he : 1 ≤ Real.exp ((-1/100)*(unitObs false N-(9/10)*(V:ℝ))) :=
      Real.one_le_exp_iff.mpr (by simpa [unitObs] using (show 0 ≤ (-1/100)*(wCount N-(9/10)*(V:ℝ)) by linarith))
    linarith
  · have he : 1 ≤ Real.exp ((1/100)*(unitObs false N-(11/10)*(V:ℝ))) :=
      Real.one_le_exp_iff.mpr (by simpa [unitObs] using (show 0 ≤ (1/100)*(wCount N-(11/10)*(V:ℝ)) by linarith))
    linarith

theorem generator_add {α β : Type*} [Fintype α] [Fintype β]
    (M : FiniteJumpModel α β) (f g : α → ℝ) (x : α) :
    M.generator (fun y => f y+g y) x = M.generator f x+M.generator g x := by
  unfold FiniteJumpModel.generator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem stopped_resource_foster (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (N : BoxCounts V) :
    (stoppedModel V eps k r hV heps hk hr).generator
      (fun X => resourcePotential V (boxCounts X)) N ≤ 4*resourceSource V := by
  unfold resourcePotential
  simp only [generator_add]
  have hu := stopped_upper_foster true V eps k r hV heps heps1 hk hk1 hr hr22 N
  have hlu := stopped_lower_foster true V eps k r hV heps heps1 hk hk1 hr hr22 N
  have hw := stopped_upper_foster false V eps k r hV heps heps1 hk hk1 hr hr22 N
  have hlw := stopped_lower_foster false V eps k r hV heps heps1 hk hk1 hr hr22 N
  linarith

theorem stopped_resource_probability (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (q t : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ N, (stoppedModel V eps k r hV heps hk hr).total N ≤ q)
    (N : BoxCounts V) :
    ((stoppedModel V eps k r hV heps hk hr).uniformize q hq hbound).poissonized
      (q*t) (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) N ≤
      resourcePotential V (boxCounts N)+(t:ℝ)*(4*resourceSource V) := by
  have h := (stoppedModel V eps k r hV heps hk hr).uniformized_event_bound q t hq hbound
    {X | ¬resourceGood (boxCounts X) V} (fun X => resourcePotential V (boxCounts X))
    1 (4*resourceSource V) (fun X => resourcePotential_nonneg V (boxCounts X))
    (fun X hX => resourcePotential_exit V (boxCounts X) hX)
    (stopped_resource_foster V eps k r hV heps heps1 hk hk1 hr hr22) N
  simpa only [one_mul] using h

def foodInitial (V : ℕ) : BoxCounts V :=
  ![⟨V,by omega⟩,⟨V,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩,⟨0,by omega⟩]

theorem foodInitial_units (V : ℕ) (side : Bool) :
    unitObs side (boxCounts (foodInitial V)) = V := by
  cases side <;> simp [unitObs,uCount_expansion,wCount_expansion,boxCounts,foodInitial]

theorem foodInitial_potential (V : ℕ) :
    resourcePotential V (boxCounts (foodInitial V)) = 4*Real.exp (-(V:ℝ)/1000) := by
  unfold resourcePotential upperUnitPotential lowerUnitPotential
  rw [foodInitial_units,foodInitial_units]
  have h₁ : (1/100)*((V:ℝ)-(11/10)*V) = -(V:ℝ)/1000 := by ring
  have h₂ : (-1/100)*((V:ℝ)-(9/10)*V) = -(V:ℝ)/1000 := by ring
  rw [h₁,h₂]
  ring

/-- Resource exit for the exact stopped count model, with a food-only initial state.
The stopped dynamics retain the first exiting state; no transition is reflected. -/
theorem evaluated_resource_probability (eps k r : ℝ)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (q : ℝ≥0) (hq : 0 < (q:ℝ))
    (hbound : ∀ N, (stoppedModel 100000000 eps k r (by norm_num) heps hk hr).total N ≤ q) :
    ((stoppedModel 100000000 eps k r (by norm_num) heps hk hr).uniformize q hq hbound).poissonized
      (q*1000) (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) 100000000})
      (foodInitial 100000000) < 1/10000 := by
  have h := stopped_resource_probability 100000000 eps k r (by norm_num)
    heps heps1 hk hk1 hr hr22 q 1000 hq hbound (foodInitial 100000000)
  rw [foodInitial_potential] at h
  norm_num [resourceSource] at h
  have hb := evaluated_resource_budget
  norm_num at hb
  linarith

end
end RandomViability.Binding

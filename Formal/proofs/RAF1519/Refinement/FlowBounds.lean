import proofs.RAF1519.Refinement.SourceFlow
import proofs.RAF1519.Refinement.IntermediateBounds
import proofs.RAF1519.Refinement.Pulse
import proofs.ProductiveRecovery.StrongMaterial

namespace RAF1519.Refinement
noncomputable section
open CoreCouplingGlobal

theorem coordinate_bound (c : State) (hc : ∀ i, 0 ≤ c i)
    (ha : materialA c ≤ 11/10) (hb : materialB c ≤ 11/10) : ∀ i, c i ≤ 11/10 := by
  simp [materialA,materialB,free,ProductiveRecovery.A,ProductiveRecovery.B] at ha hb
  intro i
  fin_cases i
  · change c 0 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 1 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 2 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 3 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 4 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 5 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]
  · change c 6 ≤ (11/10:ℝ)
    linarith [hc 0,hc 1,hc 2,hc 3,hc 4,hc 5,hc 6]

theorem material_corridor (r d beta theta : ℝ) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d beta theta (X t)) t)
    (hA0 : 19/20 ≤ materialA (X 0) ∧ materialA (X 0) ≤ 11/10)
    (hB0 : 19/20 ≤ materialB (X 0) ∧ materialB (X 0) ≤ 11/10) :
    ∀ t, 0 ≤ t →
      (19/20 ≤ materialA (X t) ∧ materialA (X t) ≤ 11/10) ∧
      (19/20 ≤ materialB (X t) ∧ materialB (X t) ≤ 11/10) := by
  have hda : ∀ t, 0 ≤ t → HasDerivAt (fun s => materialA (X s)) (1-materialA (X t)) t := by
    intro t ht; simpa only [material_A] using deriv_material_A X _ t (hX t ht)
  have hdb : ∀ t, 0 ≤ t → HasDerivAt (fun s => materialB (X s)) (1-materialB (X t)) t := by
    intro t ht; simpa only [material_B] using deriv_material_B X _ t (hX t ht)
  have haL := scalar_lower_barrier _ _ (19/20) hda hA0.1 (fun _ _ hs => by linarith)
  have haU := scalar_upper_barrier _ _ (11/10) hda hA0.2 (fun _ _ hs => by linarith)
  have hbL := scalar_lower_barrier _ _ (19/20) hdb hB0.1 (fun _ _ hs => by linarith)
  have hbU := scalar_upper_barrier _ _ (11/10) hdb hB0.2 (fun _ _ hs => by linarith)
  exact fun t ht => ⟨⟨haL t ht,haU t ht⟩,⟨hbL t ht,hbU t ht⟩⟩

theorem intermediate_ceiling (r d theta : ℝ) (hd : 0 ≤ d) (ht : 0 < theta)
    (X : ℝ → State) (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d (1/100) theta (X t)) t)
    (hA : ∀ t, 0 ≤ t → materialA (X t) ≤ 11/10)
    (hB : ∀ t, 0 ≤ t → materialB (X t) ≤ 11/10)
    (hb0 : X 0 6 ≤ (1101/1000)*theta) :
    ∀ t, 0 ≤ t → X t 6 ≤ (1101/1000)*theta := by
  apply scalar_upper_barrier (fun t => X t 6)
    (fun t => field r d (1/100) theta (X t) 6) ((1101/1000)*theta)
    (fun t ht => hasDerivAt_pi.1 (hX t ht) 6) hb0
  intro t ht0 hhigh
  have hc := coordinate_bound (X t) (hn t ht0) (hA t ht0) (hB t ht0)
  have hf := forcing_bound (X t) (hn t ht0) (hc 0) (hc 1) (hc 2)
  have hdiv : (1101/1000:ℝ) ≤ X t 6/theta := (le_div_iff₀ ht).2 hhigh
  have hgap : forcing (1/100) (X t)-X t 6/theta ≤ 0 := by linarith
  have hp := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ d*(1+1/100) by linarith) hgap
  rw [intermediate_filter r d (1/100) theta (X t) (by norm_num)]
  have hn6 := hn t ht0 6
  linear_combination hp + hn6

theorem free_corridor (c : State) (theta : ℝ) (ht : theta ≤ 1/100)
    (ha : 19/20 ≤ materialA c) (hb : 19/20 ≤ materialB c)
    (hd : c 6 ≤ (1101/1000)*theta) :
    9/10 ≤ ProductiveRecovery.A (free c) ∧ 9/10 ≤ ProductiveRecovery.B (free c) := by
  dsimp [materialA,materialB] at ha hb
  constructor <;> linarith

theorem material_return (r d beta theta : ℝ) (X : ℝ → State)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (field r d beta theta (X t)) t)
    (hA0 : 19/20 ≤ materialA (X 0) ∧ materialA (X 0) ≤ 11/10)
    (hB0 : 19/20 ≤ materialB (X 0) ∧ materialB (X 0) ≤ 11/10) :
    ∀ t, 3 ≤ t → (159/160 ≤ materialA (X t) ∧ materialA (X t) ≤ 161/160) ∧
      (159/160 ≤ materialB (X t) ∧ materialB (X t) ≤ 161/160) := by
  have hda : ∀ t, 0 ≤ t → HasDerivAt (fun s => materialA (X s)) (1-materialA (X t)) t := by
    intro t ht; simpa only [material_A] using deriv_material_A X _ t (hX t ht)
  have hdb : ∀ t, 0 ≤ t → HasDerivAt (fun s => materialB (X s)) (1-materialB (X t)) t := by
    intro t ht; simpa only [material_B] using deriv_material_B X _ t (hX t ht)
  exact fun t ht => ⟨ProductiveRecovery.strong_material_interior _ hda
    ⟨by linarith [hA0.1],hA0.2⟩ t ht,ProductiveRecovery.strong_material_interior _ hdb
    ⟨by linarith [hB0.1],hB0.2⟩ t ht⟩
end
end RAF1519.Refinement

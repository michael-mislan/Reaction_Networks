import proofs.RAF1519.Reservoir.CommunityAttraction

namespace RAF1519.Reservoir
noncomputable section
open Set Filter Topology
open scoped BigOperators

/-- An open neighborhood of positive global trajectories converging to the center. -/
def LocallyAttracting {n : ℕ} (q : Fin n → ℝ) (c : Community n) : Prop :=
  ∃ ε > 0, ∀ x₀, dist x₀ c < ε →
    ∃ X : ℝ → Community n, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt X (communityField q (X t)) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 < X t i) ∧ Tendsto X atTop (𝓝 c)

def communityUptake {n : ℕ} (x : Community n) : ℝ :=
  x (.inl 4)*x (.inl 2)*totalConsumers x

theorem uptake_lift {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) : communityUptake (lift q s) = uptake s := by
  unfold communityUptake
  rw [total_lift q hq s]
  change reservoir s*resource s*s = uptake s
  have hR : reservoir s ≠ 0 := ne_of_gt (reservoir_positive s hs)
  unfold resource uptake
  field_simp

/-- Two positive locally attracting communities with identical prescribed
consumer proportions and strictly separated total abundance and uptake. -/
theorem R19 {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1)
    (hpos : ∀ i, 0 < q i) :
    ∃ c₁ c₂ : Community n,
      (∀ i, 0 < c₁ i) ∧ (∀ i, 0 < c₂ i) ∧
      communityField q c₁ = 0 ∧ communityField q c₂ = 0 ∧
      (∀ i, c₁ (.inr i)/totalConsumers c₁ = q i) ∧
      (∀ i, c₂ (.inr i)/totalConsumers c₂ = q i) ∧
      totalConsumers c₁ < totalConsumers c₂ ∧ communityUptake c₁ < communityUptake c₂ ∧
      LocallyAttracting q c₁ ∧ LocallyAttracting q c₂ := by
  obtain ⟨a,b,ha,hb,hab,_,_,hfa,hfb⟩ := two_positive_stationary_states
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := ha0.trans hab
  have haI : a ∈ Icc (0:ℝ) (3/40) := ⟨ha0.le,by linarith [ha.2]⟩
  have hbI : b ∈ Icc (0:ℝ) (3/40) := ⟨hb0.le,by linarith [hb.2]⟩
  have hpa := lift_positive q hpos a haI ha0
  have hpb := lift_positive q hpos b hbI hb0
  have hba := low_root_box a ha
  have hbb := high_root_box b hb
  refine ⟨lift q a,lift q b,hpa,hpb,lift_stationary q hq hpos a haI hfa,
    lift_stationary q hq hpos b hbI hfb,prescribed_composition q hq a ha0,
    prescribed_composition q hq b hb0,?_,?_,?_,?_⟩
  · simpa only [total_lift q hq] using hab
  · rw [uptake_lift q hq a haI,uptake_lift q hq b hbI]
    unfold uptake
    nlinarith [mul_pos (sub_pos.mpr hab) (show 0 < a+b by linarith)]
  · exact community_attraction lowP q hq hpos a lowBoxLower lowBoxUpper
      (by linarith [ha.1]) hfa hpa hba low_core_coercive
      (fun x hx => low_core_decay x (state a) hfa hx (fun i => ⟨(hba i).1.le,(hba i).2.le⟩))
  · exact community_attraction highP q hq hpos b highBoxLower highBoxUpper
      (by linarith [hb.1]) hfb hpb hbb high_core_coercive
      (fun x hx => high_core_decay x (state b) hfb hx (fun i => ⟨(hbb i).1.le,(hbb i).2.le⟩))

#print axioms R19

end
end RAF1519.Reservoir

import proofs.RAF1519.Reservoir.Attractors

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def compositionDiscrepancy {n : ℕ} (q p : Fin n → ℝ) : ℝ :=
  ∑ i, (p i-q i)^2/q i

theorem variance_composition {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∀ i, 0 < q i) (hS : totalConsumers x ≠ 0) :
    variance q (normalizedDeviation q x) = (totalConsumers x)^2 *
      compositionDiscrepancy q (fun i => x (.inr i)/totalConsumers x) := by
  unfold variance compositionDiscrepancy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold normalizedDeviation
  have hqi := (hq i).ne'
  field_simp

theorem transient_uptake {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) :
    communityUptake x = totalConsumers (communityField q x) +
      (1/2)*totalConsumers x+(totalConsumers x)^2+variance q (normalizedDeviation q x) := by
  rw [total_source q x hq hpos]
  unfold communityUptake
  ring

theorem transient_composition_readout {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i) (hS : totalConsumers x ≠ 0) :
    communityUptake x = totalConsumers (communityField q x)+(1/2)*totalConsumers x+
      (totalConsumers x)^2*(1+compositionDiscrepancy q (fun i => x (.inr i)/totalConsumers x)) := by
  rw [transient_uptake q x hq hpos, variance_composition q x hpos hS]
  ring

theorem abundance_readout_error (J S D W M Smax ν ξ ε : ℝ)
    (hid : J = D+(1/2)*S+S^2+W)
    (hS : 0 ≤ S) (hSm : S ≤ Smax) (hξ : 0 ≤ ξ) (hε : 0 ≤ ε)
    (hD : |D| ≤ ν) (hW : 0 ≤ W) (hWm : W ≤ S^2*ξ) (hM : |M-S| ≤ ε) :
    |J-((1/2)*M+M^2)| ≤ ν+Smax^2*ξ+(1/2+2*Smax)*ε+ε^2 := by
  have hSm0 : 0 ≤ Smax := hS.trans hSm
  have hsq : S^2 ≤ Smax^2 := by nlinarith
  have hw : W ≤ Smax^2*ξ := hWm.trans (mul_le_mul_of_nonneg_right hsq hξ)
  have hm := abs_le.mp hM
  have hd := abs_le.mp hD
  have he : (M-S)^2 ≤ ε^2 := by nlinarith
  have hlo : -(2*Smax*ε) ≤ 2*S*(M-S) := by
    nlinarith [mul_nonneg hS (show 0 ≤ M-S+ε by linarith),
      mul_nonneg hε (sub_nonneg.mpr hSm)]
  have hhi : 2*S*(M-S) ≤ 2*Smax*ε := by
    nlinarith [mul_nonneg hS (show 0 ≤ ε-(M-S) by linarith),
      mul_nonneg hε (sub_nonneg.mpr hSm)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (M-S)]

theorem stationary_supply_cap {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i)
    (hx : ∀ i, 0 ≤ x i) (heq : communityField q x=0) :
    x (.inl 4)*totalConsumers x ≤ 1/40 := by
  have hr := congrFun heq (.inl 4)
  change (1/20)*(1-x (.inl 4))-communityUptake x=0 at hr
  have hs : totalConsumers (communityField q x)=0 := by rw [heq]; simp [totalConsumers]
  have hu := transient_uptake q x hq hpos
  rw [hs] at hu
  have hv := variance_nonnegative q (normalizedDeviation q x) (fun i => (hpos i).le)
  have hR := hx (.inl 4)
  have hb : (1/2)*totalConsumers x ≤ (1/20)*(1-x (.inl 4)) := by
    nlinarith [sq_nonneg (totalConsumers x)]
  have hm := mul_le_mul_of_nonneg_left hb hR
  nlinarith [sq_nonneg (x (.inl 4)-1/2)]

/-- The stationary load bound cannot be extended to arbitrary positive states. -/
theorem transient_load_counterexample : (1:ℝ)*(1/10) > 1/40 := by norm_num

#print axioms transient_composition_readout
#print axioms stationary_supply_cap
end
end RAF1519.Reservoir

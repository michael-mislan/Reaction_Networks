import proofs.RAF1519.Reservoir.FeedbackLoad

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

/-- A rational certificate within 8e-8 of the maximum necessary load. -/
theorem stationary_load_rational_bound (S : ℝ) (hS : 0 ≤ S) :
    stationaryLoad S ≤ 2239911/97656250 := by
  have hid : (2239911/97656250:ℝ)-stationaryLoad S =
      10*(S-11/250-(12/3125)/20)^2 + 20*(S+2*(11/250))*(S-11/250)^2 := by
    unfold stationaryLoad
    ring
  have hterm : 0 ≤ 20*(S+2*(11/250:ℝ))*(S-11/250)^2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [sq_nonneg (S-11/250-(12/3125)/20)]

/-- Source-bound stationary cap, including boundary consumer states. -/
theorem sharp_stationary_supply_cap {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i)
    (hx : ∀ i, 0 ≤ x i) (heq : communityField q x=0) :
    x (.inl 4)*totalConsumers x ≤ 2239911/97656250 := by
  have hS : 0 ≤ totalConsumers x := Finset.sum_nonneg (fun i _ => hx (.inr i))
  have hr := congrFun heq (.inl 4)
  change (1/20)*(1-x (.inl 4))-communityUptake x=0 at hr
  have hs : totalConsumers (communityField q x)=0 := by rw [heq]; simp [totalConsumers]
  have hu := transient_uptake q x hq hpos
  rw [hs] at hu
  have hv := variance_nonnegative q (normalizedDeviation q x) (fun i => (hpos i).le)
  have hb : x (.inl 4) ≤ 1-10*totalConsumers x-20*(totalConsumers x)^2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hb hS
  have hc := stationary_load_rational_bound (totalConsumers x) hS
  unfold stationaryLoad at hc
  nlinarith only [hm,hc]

#print axioms sharp_stationary_supply_cap
end
end RAF1519.Reservoir

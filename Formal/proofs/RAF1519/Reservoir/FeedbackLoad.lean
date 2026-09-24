import proofs.RAF1519.Reservoir.WindowReadout
import proofs.ProductiveMemory.ExtractionEquilibria

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators

def residentProjection {n : ℕ} (x : Community n) : Fin 4 → ℝ := fun i => x (.inl i.castSucc)

/-- Only the deterministic resident drift is identified; no protocol or law is transferred. -/
theorem resident_feedback_identity {n : ℕ} (q : Fin n → ℝ) (x : Community n) :
    residentProjection (communityField q x) =
      ProductiveMemory.extractDrift (x (.inl 4)*totalConsumers x) 0 (residentProjection x) := by
  unfold ProductiveMemory.extractDrift
  rw [FiniteCopy.drift_formula]
  funext i
  fin_cases i <;>
    dsimp [residentProjection,communityField,aggregate,field,totalConsumers] <;> ring

def stationaryLoad (S : ℝ) : ℝ := S-10*S^2-20*S^3

theorem stationary_load_curve {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i)
    (heq : communityField q x=0) (hcomp : normalizedDeviation q x=0) :
    communityUptake x = uptake (totalConsumers x) ∧
    x (.inl 4)*totalConsumers x=stationaryLoad (totalConsumers x) := by
  have ht := transient_uptake q x hq hpos
  have hs : totalConsumers (communityField q x)=0 := by rw [heq]; simp [totalConsumers]
  rw [hs,hcomp] at ht
  have hz : variance q 0=0 := by simp [variance]
  rw [hz] at ht
  have hr := congrFun heq (.inl 4)
  change (1/20)*(1-x (.inl 4))-communityUptake x=0 at hr
  constructor
  · unfold uptake; nlinarith
  · unfold stationaryLoad
    have he : x (.inl 4)=1-10*totalConsumers x-20*(totalConsumers x)^2 := by linarith
    rw [he]; ring

theorem supply_cap_below_exclusion {n : ℕ} (q : Fin n → ℝ) (x : Community n)
    (hq : ∑ i, q i=1) (hpos : ∀ i, 0 < q i)
    (hx : ∀ i, 0 ≤ x i) (heq : communityField q x=0) :
    x (.inl 4)*totalConsumers x < 31/1000 := by
  linarith [stationary_supply_cap q x hq hpos hx heq]

end
end RAF1519.Reservoir

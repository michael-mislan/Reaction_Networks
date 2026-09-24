import proofs.RandomViability.Startup
import proofs.RandomViability.BoundedMassDrift

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def foodCountSupported {n : ℕ} (N : Molecule n → ℕ) : Prop :=
  ∀ z, 0 < N z → z ∈ binaryFood n 2

theorem enabled_food_catalysis_implies_ignition {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (hN : foodCountSupported N) (r : Reaction n) (z : Molecule n) (d : Bool)
    (hsel : r ∈ c z) (hen : ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ N x) :
    FoodIgnition c := by
  have hz : z ∈ binaryFood n 2 := by
    apply hN
    have hh := hen z
    cases d <;> simp [physicalChannelInput, singleCount] at hh <;> omega
  refine ⟨z,hz,r,?_,hsel⟩
  cases d with
  | false =>
    apply Or.inr
    intro x hx
    have he : x=reactionProduct r := by simpa [binaryPolymerCRS] using hx
    subst x
    apply hN
    have hh := hen (reactionProduct r)
    simp [physicalChannelInput, singleCount] at hh
    omega
  | true =>
    apply Or.inl
    intro x hx
    have he : x=reactionLeft r ∨ x=reactionRight r := by simpa [binaryPolymerCRS] using hx
    rcases he with rfl | rfl
    · apply hN
      have hh := hen (reactionLeft r)
      simp [physicalChannelInput, singleCount] at hh
      omega
    · apply hN
      have hh := hen (reactionRight r)
      simp [physicalChannelInput, singleCount] at hh
      omega

theorem bounded_food_catalytic_rate_zero {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (hc : ¬ FoodIgnition c) (V D : NNReal) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (hN : foodCountSupported (boundedCountsValue N)) (r : Reaction n) (z : Molecule n) (d : Bool) :
    (boundedPhysicalCountModel c V D basal cat).rate N (.inr (.inr (r,z,d))) = 0 := by
  change (if ∀ x, physicalChannelInput (.inr (.inr (r,z,d))) x ≤ boundedCountsValue N x then
    physicalChannelRate c V D basal cat (boundedCountsValue N) (.inr (.inr (r,z,d))) else 0) = 0
  split_ifs with hen
  · by_cases hs : r ∈ c z
    · exact False.elim (hc (enabled_food_catalysis_implies_ignition c (boundedCountsValue N) hN r z d hs hen))
    · simp [physicalChannelRate, physicalChannelCoefficient, hs]
  · rfl

theorem bounded_food_reference_internal_zero {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (hc : ¬ FoodIgnition c) (V D : NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (hN : foodCountSupported (boundedCountsValue N))
    (ch : (Reaction n × Bool) ⊕ (Reaction n × Molecule n × Bool)) :
    (boundedPhysicalCountModel c V D (fun _ => 0) cat).rate N (.inr ch) = 0 := by
  cases ch with
  | inl r => simp [boundedPhysicalCountModel, physicalChannelRate, physicalChannelCoefficient]
  | inr r => exact bounded_food_catalytic_rate_zero c hc V D _ cat N hN r.1 r.2.1 r.2.2

theorem bounded_food_reference_generator {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (hc : ¬ FoodIgnition c) (V D : NNReal) (hV : 0 < (V : ℝ))
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (hN : foodCountSupported (boundedCountsValue N)) (f : BoundedCounts n B → ℝ) :
    (boundedPhysicalCountModel c V D (fun _ => 0) cat).generator f N =
      (∑ z : ↥(binaryFood n 2), (D : ℝ)*V*(f ((boundedPhysicalCountModel c V D (fun _ => 0) cat).next N (.inl (.inl z)))-f N)) +
      ∑ z : Molecule n, (D : ℝ)*boundedCountsValue N z*(f ((boundedPhysicalCountModel c V D (fun _ => 0) cat).next N (.inl (.inr z)))-f N) := by
  unfold FiniteJumpModel.generator
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hi : (∑ ch : (Reaction n × Bool) ⊕ (Reaction n × Molecule n × Bool),
      (boundedPhysicalCountModel c V D (fun _ => 0) cat).rate N (.inr ch)*
        (f ((boundedPhysicalCountModel c V D (fun _ => 0) cat).next N (.inr ch))-f N)) = 0 := by
    apply Finset.sum_eq_zero
    intro ch _
    rw [bounded_food_reference_internal_zero c hc V D cat N hN ch, zero_mul]
  rw [hi, add_zero]
  simp_rw [bounded_food_rate, bounded_outflow_rate c V D hV]

end
end RandomViability

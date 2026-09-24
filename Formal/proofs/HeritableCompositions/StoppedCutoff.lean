import proofs.HeritableCompositions.StoppedGrowth
import proofs.HeritableCompositions.AffineRecovery

namespace HeritableCompositions
open FiniteCopy

noncomputable def activeObservable (N : ℕ) (D : Finset Compartment) (f : Compartment → ℝ) :
    StoppedCompartment D → ℝ
  | none => 0
  | some c => if c.val.2 < 2*N then f c.val else 0

theorem activeObservable_nonneg (N : ℕ) (D : Finset Compartment) (f : Compartment → ℝ)
    (hf : ∀ c, 0 ≤ f c) (c : StoppedCompartment D) : 0 ≤ activeObservable N D f c := by
  cases c with
  | none => exact le_rfl
  | some c => dsimp [activeObservable]; split_ifs <;> first | exact hf c.val | exact le_rfl

theorem active_generator_le (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (D : Finset Compartment)
    (f : Compartment → ℝ) (hf : ∀ c, 0 ≤ f c) (c : {c : Compartment // c ∈ D})
    (hc : c.val.2 < 2*N) :
    (stoppedGrowthModel γ hγ N D).generator (activeObservable N D f) (some c) ≤
      compartmentGenerator γ f c.val := by
  classical
  unfold FiniteJumpModel.generator compartmentGenerator
  apply Finset.sum_le_sum
  intro r _
  have hn : activeObservable N D f ((stoppedGrowthModel γ hγ N D).next (some c) r) ≤
      f (nextCompartment c.val r) := by
    by_cases hd : nextCompartment c.val r ∈ D
    · by_cases ha : (nextCompartment c.val r).2 < 2*N
      · simp [stoppedGrowthModel,hc,hd,activeObservable,ha]
      · simpa [stoppedGrowthModel,hc,hd,activeObservable,ha] using hf (nextCompartment c.val r)
    · simpa [stoppedGrowthModel,hc,hd,activeObservable] using hf (nextCompartment c.val r)
  simpa [stoppedGrowthModel,hc,activeObservable] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hn (f c.val)) (propensity_nonneg γ hγ c.val r)

theorem retained_affine_event (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (D : Finset Compartment)
    (f : Compartment → ℝ) (hf : ∀ c, 0 ≤ f c) (k C : ℝ) (hk0 : 0 ≤ k) (hC : 0 ≤ C)
    (hgen : ∀ c ∈ D, c.2 < 2*N → compartmentGenerator γ f c ≤ -k*f c+k*C)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q) (hk : k ≤ q)
    (A : Set (StoppedCompartment D)) (a : ℝ)
    (hA : ∀ c ∈ A, a ≤ activeObservable N D f c)
    (c : {c : Compartment // c ∈ D}) (hc : c.val.2 < 2*N) :
    a*((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤ Real.exp (-k*(t : ℝ))*f c.val+C := by
  have hp : 0 ≤ k*C := mul_nonneg hk0 hC
  have hG : ∀ x, (stoppedGrowthModel γ hγ N D).generator (activeObservable N D f) x ≤
      -k*activeObservable N D f x+k*C := by
    intro x
    cases x with
    | none => simpa [stoppedGrowthModel,FiniteJumpModel.generator,activeObservable] using hp
    | some x =>
      by_cases hx : x.val.2 < 2*N
      · have h := (active_generator_le γ hγ N D f hf x hx).trans (hgen x.val x.property hx)
        simpa only [activeObservable,if_pos hx] using h
      · simpa [stoppedGrowthModel,FiniteJumpModel.generator,hx,activeObservable] using hp
  have h := uniformized_event_affine (stoppedGrowthModel γ hγ N D) q t hq hclock
    A (activeObservable N D f) a k C (activeObservable_nonneg N D f hf) hA hk hC hG (some c)
  simpa only [activeObservable,if_pos hc] using h

end HeritableCompositions

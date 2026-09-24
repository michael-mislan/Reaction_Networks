import proofs.HeritableCompositions.MembraneClock
import proofs.HeritableCompositions.KilledRecovery

namespace HeritableCompositions
open FiniteCopy

theorem stopped_early_clock (γ b : ℝ) (hγ : 0 ≤ γ) (hb : 0 ≤ b)
    (N : ℕ) (D : Finset Compartment)
    (hrate : ∀ c ∈ D, c.2 < 2*N → γ*(c.1 2 : ℝ) ≤ 2*b*(N : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q)
    (A : Set (StoppedCompartment D)) (a : ℝ)
    (hA : ∀ c ∈ A, a ≤ growthObservable D (membraneObservable N (1/5)) 0 c)
    (c : {c : Compartment // c ∈ D}) :
    a*((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤
      Real.exp ((12*b*(N : ℝ)/25)*(t : ℝ))*membraneObservable N (1/5) c.val := by
  classical
  let W := growthObservable D (membraneObservable N (1/5)) 0
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    cases x with
    | none => exact le_rfl
    | some x => exact (Real.exp_pos _).le
  have hgen : ∀ x, (stoppedGrowthModel γ hγ N D).generator W x ≤
      -(-(12*b*(N : ℝ)/25))*W x := by
    intro x
    cases x with
    | none => simp [stoppedGrowthModel,FiniteJumpModel.generator,W,growthObservable]
    | some x =>
      by_cases hx : x.val.2 < 2*N
      · have hh := (stopped_growth_generator_le γ hγ N D (membraneObservable N (1/5)) 0
          (fun _ _ _ _ _ => (Real.exp_pos _).le) x hx).trans
          (early_membrane_generator γ b hγ N x.val (hrate x.val x.property hx))
        simpa only [neg_neg] using hh
      · have hp : 0 ≤ (12*b*(N : ℝ)/25)*membraneObservable N (1/5) x.val := by
          unfold membraneObservable
          positivity
        simpa [stoppedGrowthModel,FiniteJumpModel.generator,hx,W,growthObservable] using hp
  have hk : -(12*b*(N : ℝ)/25) ≤ q := by
    have hp : 0 ≤ 12*b*(N : ℝ)/25 := by positivity
    linarith only [hq,hp]
  have hh := uniformized_event_exponential (stoppedGrowthModel γ hγ N D) q t hq hclock
    A W a (-(12*b*(N : ℝ)/25)) hW hA hk hgen (some c)
  simpa only [neg_neg] using hh

theorem killed_late_clock (γ a : ℝ) (hγ : 0 ≤ γ) (ha : 0 ≤ a)
    (N : ℕ) (D : Finset Compartment) (hD : ∀ c ∈ D, c.2 < 2*N)
    (hrate : ∀ c ∈ D, a*(N : ℝ) ≤ γ*(c.1 2 : ℝ))
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N D).total c ≤ q)
    (hk : 19*a*(N : ℝ)/400 ≤ q)
    (A : Set (StoppedCompartment D)) (threshold : ℝ)
    (hA : ∀ c ∈ A, threshold ≤ growthObservable D (membraneObservable N (-1/20)) 0 c)
    (c : {c : Compartment // c ∈ D}) :
    threshold*((stoppedGrowthModel γ hγ N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤
      Real.exp (-(19*a*(N : ℝ)/400)*(t : ℝ))*membraneObservable N (-1/20) c.val := by
  have hgen (d) (hd : d ∈ D) : compartmentGenerator γ (membraneObservable N (-1/20)) d ≤
      -(19*a*(N : ℝ)/400)*membraneObservable N (-1/20) d+(19*a*(N : ℝ)/400)*0 := by
    simpa only [mul_zero,add_zero] using late_membrane_generator γ a hγ N d (hrate d hd)
  have h := killed_growth_affine_bound γ hγ N D hD (membraneObservable N (-1/20))
    (fun _ => (Real.exp_pos _).le) (19*a*(N : ℝ)/400) 0 (by positivity) (by norm_num)
    hgen q t hq hclock hk A threshold hA c
  simpa only [add_zero] using h

end HeritableCompositions

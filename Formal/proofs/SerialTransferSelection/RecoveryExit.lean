import proofs.SerialTransferSelection.RecoverySource

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

theorem recovery_exit_scalar (u p : ℝ)
    (h : Real.exp (16*u)*p ≤ Real.exp (8*u)+16*u*Real.exp (u/2)) :
    p ≤ Real.exp (-8*u)+16*u*Real.exp (-31*u/2) := by
  calc
    p ≤ (Real.exp (8*u)+16*u*Real.exp (u/2))/Real.exp (16*u) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa [mul_comm] using h
    _ = _ := by
      rw [add_div, mul_div_assoc, ← Real.exp_sub, ← Real.exp_sub]
      rw [show 8*u-16*u = -8*u by ring,
        show u/2-16*u = -31*u/2 by ring]

/-- Exit error from the same finite law as terminal recovery. Its boundary
comparison uses the raw outgoing count state, including overshoots. -/
theorem endpoint_exit_recovery (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N)
    (s : Point) (hs : ∀ i, s i ≤ 34) (E : Point → ℝ)
    (hE : ∀ y, (1/200)*normSq y ≤ E y)
    (hgen : ∀ c ∈ growthDomain N s E outerEnergy, c.2 < 2*N →
      compartmentGenerator γ (fun d => Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration d.2 d.1 i-s i))) c ≤
      -((N : ℝ)*localAlpha*innerEnergy/672)*Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration c.2 c.1 i-s i))+
      ((N : ℝ)*localAlpha*innerEnergy/672)*(2*Real.exp ((N : ℝ)*localAlpha*innerEnergy/2)))
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).total c ≤ q)
    (c : {c : Compartment // c ∈ growthDomain N s E outerEnergy})
    (hendpoint : E (fun i => concentration c.val.2 c.val.1 i-s i) ≤ 8*innerEnergy) :
    ((stoppedGrowthModel γ hγ N (growthDomain N s E outerEnergy)).uniformize q hq hclock).poissonized
      (q*5376) (FiniteKernel.eventIndicator {none}) (some c) ≤
      Real.exp (-8*((N : ℝ)*localAlpha*innerEnergy))+
        16*((N : ℝ)*localAlpha*innerEnergy)*Real.exp (-31*((N : ℝ)*localAlpha*innerEnergy)/2) := by
  let u := (N : ℝ)*localAlpha*innerEnergy
  have hu : 0 ≤ u := by dsimp [u,localAlpha,innerEnergy,outerEnergy]; positivity
  have hg : ∀ d ∈ growthDomain N s E outerEnergy, d.2 < 2*N →
      compartmentGenerator γ (fun e => Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration e.2 e.1 i-s i))) d ≤
        (u/672)*(2*Real.exp (u/2)) := by
    intro d hd hm
    have h := hgen d hd hm
    have hn : 0 ≤ (u/672)*Real.exp ((N : ℝ)*localAlpha*
        E (fun i => concentration d.2 d.1 i-s i)) := by positivity
    linarith only [h, hn]
  have h := growth_energy_exit_bound γ hγ N hN s hs E hE outerEnergy
    ((u/672)*(2*Real.exp (u/2))) (by norm_num [outerEnergy]) (by positivity)
    hg q 5376 hq hclock c
  have hb : (N : ℝ)*localAlpha*outerEnergy = 16*u := by
    dsimp [u,innerEnergy]
    ring
  have ht : (5376 : NNReal)*((u/672)*(2*Real.exp (u/2))) =
      16*u*Real.exp (u/2) := by norm_num; ring
  rw [hb, ht] at h
  have hi : Real.exp ((N : ℝ)*localAlpha*
      E (fun i => concentration c.val.2 c.val.1 i-s i)) ≤ Real.exp (8*u) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hendpoint
      (by unfold localAlpha; positivity : 0 ≤ (N : ℝ)*localAlpha)
    dsimp [u]
    nlinarith only [hh]
  exact recovery_exit_scalar u _ (h.trans (add_le_add hi le_rfl))

end SerialTransferSelection

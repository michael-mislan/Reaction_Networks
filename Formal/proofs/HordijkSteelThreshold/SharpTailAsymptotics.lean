import proofs.HordijkSteelThreshold.GatewayProbability

namespace HordijkSteelThreshold

open Filter Topology unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- A lower bound on catalysis mass converts the exact closed-family factor
into an exponential bound uniform in the family depth. -/
theorem closedFamilyPow_le_exp_of_mass
    (p : I) {b d : Nat} {kappa : ℝ}
    (hkappa : kappa ≤ (p : ℝ) * b) :
    (toNNReal (σ p) : ℝ) ^ (b * d) ≤ Real.exp (-kappa * d) := by
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hq0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
  calc
    (toNNReal (σ p) : ℝ) ^ (b * d) =
        (1 - (p : ℝ)) ^ (b * d) := by rfl
    _ ≤ (Real.exp (-(p : ℝ))) ^ (b * d) := by
      exact pow_le_pow_left₀ hq0 (Real.one_sub_le_exp_neg (p : ℝ)) _
    _ = Real.exp (-((p : ℝ) * b) * d) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    _ ≤ Real.exp (-kappa * d) := by
      apply Real.exp_le_exp.mpr
      have hd0 : 0 ≤ (d : ℝ) := by positivity
      nlinarith

/-- In the concrete critical window, any prospective pool occupying a fixed
positive fraction of all molecules has a closed-family factor bounded by a
geometric exponential in the family depth.  The cutoff in `n` is independent
of `d`; this is the two-scale estimate needed before choosing a large fixed
lower layer cutoff. -/
theorem eventually_closedFamilyPow_le_exp_of_macroscopic_pool
    {lambda rho kappa : ℝ} (hlambda : 0 < lambda)
    (hkappa : kappa < rho * lambda) (b : Nat → Nat)
    (hpool : ∀ᶠ n in atTop,
      rho * Fintype.card (Molecule n) ≤ (b n : ℝ)) :
    ∀ᶠ n in atTop, ∀ d : Nat,
      (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (b n * d) ≤
        Real.exp (-kappa * d) := by
  have hscaled : Tendsto
      (fun n => rho * ((catalysisP n lambda : ℝ) *
        Fintype.card (Molecule n))) atTop (nhds (rho * lambda)) := by
    exact tendsto_const_nhds.mul (catalysisP_mul_card_molecule_tendsto hlambda)
  have hmass : ∀ᶠ n in atTop,
      kappa ≤ rho * ((catalysisP n lambda : ℝ) *
        Fintype.card (Molecule n)) :=
    (hscaled.eventually_const_lt hkappa).mono fun _ h => h.le
  filter_upwards [hpool, hmass] with n hb hpn
  intro d
  apply closedFamilyPow_le_exp_of_mass
  have hp0 : 0 ≤ (catalysisP n lambda : ℝ) := (catalysisP n lambda).2.1
  calc
    kappa ≤ rho * ((catalysisP n lambda : ℝ) *
        Fintype.card (Molecule n)) := hpn
    _ = (catalysisP n lambda : ℝ) *
        (rho * Fintype.card (Molecule n)) := by ring
    _ ≤ (catalysisP n lambda : ℝ) * b n := by
      exact mul_le_mul_of_nonneg_left hb hp0

end HordijkSteelThreshold

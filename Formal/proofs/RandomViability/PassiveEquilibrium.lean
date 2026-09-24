import proofs.RandomViability.ProductiveKineticMarks

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 30000

def passiveEquilibrium {n : ℕ} (z : Molecule n) : ℝ := (1/4 : ℝ)^molLength z

theorem passive_equilibrium_pos {n : ℕ} (z : Molecule n) : 0 < passiveEquilibrium z := by
  exact pow_pos (by norm_num) _

/-- Full input multiplicities, including coincident substrates/catalysts,
enter the mass-action monomial. -/
theorem passive_monomial_mass {n : ℕ} (N : Molecule n → ℕ) :
    (∏ z, passiveEquilibrium z^(N z)) = (1/4 : ℝ)^(countMass N) := by
  simp only [passiveEquilibrium,← pow_mul]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Both directions of every literal basal and single-catalyst pair have a
common equilibrium vector; their actual heterogeneous coefficients are shared. -/
theorem passive_physical_pair_binding {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (D : NNReal) (u : KineticMarkConfig n) (r : Reaction n) (x : Molecule n) :
    (∏ z, passiveEquilibrium z^(physicalChannelInput (.inr (.inl (r,true))) z)) =
      ∏ z, passiveEquilibrium z^(physicalChannelOutput (.inr (.inl (r,true))) z) ∧
    (∏ z, passiveEquilibrium z^(physicalChannelInput (.inr (.inr (r,x,true))) z)) =
      ∏ z, passiveEquilibrium z^(physicalChannelOutput (.inr (.inr (r,x,true))) z) ∧
    physicalChannelCoefficient c D (kineticBasal u) (kineticCatalytic u) (.inr (.inl (r,true))) =
      physicalChannelCoefficient c D (kineticBasal u) (kineticCatalytic u) (.inr (.inl (r,false))) ∧
    physicalChannelCoefficient c D (kineticBasal u) (kineticCatalytic u) (.inr (.inr (r,x,true))) =
      physicalChannelCoefficient c D (kineticBasal u) (kineticCatalytic u) (.inr (.inr (r,x,false))) := by
  simp only [passive_monomial_mass]
  exact ⟨congrArg (fun k => (1/4 : ℝ)^k) (physical_basal_channel_balanced r true),
    congrArg (fun k => (1/4 : ℝ)^k) (physical_catalytic_channel_balanced r x true),rfl,rfl⟩

end
end RandomViability

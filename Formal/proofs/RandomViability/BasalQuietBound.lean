import proofs.RandomViability.BasalEnvelope

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

theorem bounded_basal_intensity_cutoff_bound {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (b m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m) (hcap : ∀ r, (basal r : ℝ) ≤ b)
    (hB : (B : ℝ) ≤ m*V) :
    boundedBasalIntensity c V D basal cat N ≤ b*V*(m^2+m) := by
  let M := polymerMass (fun z => (boundedCountsValue N z : ℝ))
  have he : M = (countMass (boundedCountsValue N) : ℝ) := by
    simp [M, polymerMass, countMass]
  have hM : M ≤ m*V := by
    rw [he]
    have hh : (countMass (boundedCountsValue N) : ℝ) ≤ B := by exact_mod_cast N.property
    exact hh.trans hB
  have hM0 : 0 ≤ M := by rw [he]; positivity
  have hsq : M^2 ≤ (m*(V : ℝ))^2 := by nlinarith
  have hh := bounded_basal_intensity_mass_bound c V D hV basal cat N b hb hcap
  calc
    _ ≤ b*(M^2/V+M) := hh
    _ ≤ b*((m*(V : ℝ))^2/V+m*V) := mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hsq hV.le) hM) hb
    _ = _ := by field_simp

/-- The proposed 624 epsilon V hazard allowance is derived from all literal
basal channels, not supplied as a reactor-rate assumption. -/
theorem bounded_physical_basal_hazard {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D ε : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (hcap : ∀ r, (basal r : ℝ) ≤ 4*ε) (hB : (B : ℝ) ≤ 12*V) :
    boundedBasalIntensity c V D basal cat N ≤ 624*ε*V := by
  have hh := bounded_basal_intensity_cutoff_bound c V D hV basal cat N (4*ε) 12
    (by positivity) (by positivity) hcap hB
  norm_num at hh
  nlinarith

theorem bounded_physical_quiet_event_lower {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D ε : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (hcap : ∀ r, (basal r : ℝ) ≤ 4*ε) (hB : (B : ℝ) ≤ 12*V)
    (q0 q1 : NNReal) (h0 : 0 < (q0 : ℝ)) (h1 : 0 < (q1 : ℝ))
    (hb0 : ∀ N : BoundedCounts n B, (boundedPhysicalCountModel c V D (fun _ => 0) cat).total N ≤ q0)
    (hb1 : ∀ N : BoundedCounts n B, (boundedPhysicalCountModel c V D basal cat).total N ≤ q1)
    (hgap : (q1 : ℝ)-q0 = 624*ε*V)
    (t : NNReal) (N : BoundedCounts n B)
    (E : (m : ℕ) → RewardPath (Option (PhysicalCountChannel n)) m → Prop) :
    Real.exp (-(624*ε*V*t)) *
      (labeledUniformize (boundedPhysicalCountModel c V D (fun _ => 0) cat) q0 h0 hb0).poissonEventMass (q0*t) N E ≤
        (labeledUniformize (boundedPhysicalCountModel c V D basal cat) q1 h1 hb1).poissonEventMass (q1*t) N
          (fun m p => E m p ∧ FiniteLabeledKernel.pathAllowed nonBasalLabel m p) := by
  have hh := bounded_basal_quiet_event_lower c V D basal cat q0 q1 h0 h1 hb0 hb1
    (fun x => by rw [hgap]; exact bounded_physical_basal_hazard c V D ε hV basal cat x hcap hB) t N E
  simpa only [hgap] using hh

end
end RandomViability

import proofs.RandomViability.BoundedUptake

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

theorem bounded_uptake_nonneg {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) : 0 ≤ boundedCatalyticUptake c V D basal catalytic N := by
  apply Finset.sum_nonneg
  intro z _
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (ligationNonfoodMassGain_bounds r).1
    ((boundedPhysicalCountModel c V D basal catalytic).nonneg N _)

/-- The Poissonized cumulative reward bound uses physical time t, and its
constant is independent of the finite model's uniformization rate. -/
theorem bounded_poisson_accumulated_uptake_bound {n B k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ ShortIncidence k c)
    (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (κ : ℝ) (hκ : 0 ≤ κ) (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ)
    (q : NNReal) (hq : 0 < (q : ℝ)) (hqD : (D : ℝ) ≤ 2*q)
    (hbound : ∀ X : BoundedCounts n B, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q)
    (N : BoundedCounts n B) (hinit : ((boundedMass N : ℝ)/V)^3 ≤ 38000) (t : NNReal) :
    poissonAccumulatedReward
      ((boundedPhysicalCountModel c V D basal catalytic).uniformize q hq hbound)
      (fun X => boundedCatalyticUptake c V D basal catalytic X / q) (q*t) N ≤
      152000*κ*V*t/(k : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hVp : 0 < (V : ℝ) := by linarith
  have hb : ∀ X : BoundedCounts n B, boundedCatalyticUptake c V D basal catalytic X / q ≤
      (4*κ*V/((k : ℝ)*q))*((boundedMass X : ℝ)/V)^3 := by
    intro X
    have hi := boundedCatalyticUptake_mass_bound c hgood V D hVp basal catalytic X κ hκ hrate
    calc
      _ = ((k : ℝ)*boundedCatalyticUptake c V D basal catalytic X)/((k : ℝ)*q) := by field_simp
      _ ≤ (4*κ*V*((boundedMass X : ℝ)/V)^3)/((k : ℝ)*q) :=
        div_le_div_of_nonneg_right hi (by positivity)
      _ = _ := by ring
  have hh := poisson_accumulated_reward_bound
    ((boundedPhysicalCountModel c V D basal catalytic).uniformize q hq hbound)
    (fun X => ((boundedMass X : ℝ)/V)^3)
    (fun X => boundedCatalyticUptake c V D basal catalytic X / q)
    (1-(D : ℝ)/(2*q)) 38000 (4*κ*V/((k : ℝ)*q))
    (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hqD)) (by positivity)
    (fun X => bounded_cubic_uniformize_step hn c V D hV basal catalytic q hq hbound X) hb
    (fun X => div_nonneg (bounded_uptake_nonneg c V D basal catalytic X) hq.le) N hinit (q*t)
  calc
    _ ≤ ((q*t : NNReal) : ℝ)*(4*κ*V/((k : ℝ)*q))*38000 := hh
    _ = _ := by
      simp only [NNReal.coe_mul]
      field_simp
      ring

end
end RandomViability

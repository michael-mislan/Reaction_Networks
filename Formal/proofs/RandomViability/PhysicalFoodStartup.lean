import proofs.RandomViability.PhysicalScalarComparison
import proofs.RandomViability.PhysicalStartupDrift
import proofs.RandomViability.CollectivePathBounds

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem physical_food_reduced_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V)
    (q : Molecule n) (hq : molLength q = 2) :
    1-1358*((N q : ℝ)/V) ≤ physicalCoordinateDrift c V basal cat N q := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hnf := (nonfoodMass_le_mass x hx).trans hm
  have hC : 4*(1/500000000 : ℝ)+(16/3)*nonfoodMass x ≤ 59 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hC (hx q)
  have hg := physical_food_drift_bound c V hV basal cat N (1/500000000) (by norm_num)
    hb hc hfood hM q hq
  change 1-x q-23*(4*(1/500000000 : ℝ)+(16/3)*nonfoodMass x)*x q ≤ _ at hg
  change 1-1358*x q ≤ _
  nlinarith only [hg,hmul]

/-- Food-only initialization plus the actual stopped compensation bound gives
the quantitative food floor at every active complete prefix. -/
theorem physical_food_prefix_floor {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (q : Molecule n) (hq : molLength q = 2) (T eta : ℝ) (heta : 0 ≤ eta)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hinit : ((z 0).1 q : ℝ)/V = 1)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i < K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i < K,0 ≤ (z (i+1)).2.2)
    (hnoise : ∀ i < K,∀ s ∈ Icc 0 (z (i+1)).2.2,
      coordinateCompensationWithinInterval c V basal cat q T z i s ≤ eta)
    (hend : -eta ≤ censoredCoordinatePrefix c V basal cat q T z K) :
    (1/1358 : ℝ)-2*eta ≤ ((z K).1 q : ℝ)/V := by
  have hd : ∀ i < K,1-1358*(((z i).1 q : ℝ)/V) ≤
      physicalCoordinateDrift c V basal cat (z i).1 q := by
    intro i hi
    have hM : (countMass (z i).1 : ℝ) ≤ 11*V :=
      not_not.mp (not_or.mp (not_or.mp (hs i hi)).2).1
    exact physical_food_reduced_drift c V hV basal cat hb hcat hfood (z i).1 hM q hq
  have hp := physical_coordinate_prefix_comparison c V basal cat q T 1358 1 eta z K
    (by norm_num) hc hs ht hh hd hnoise hend
  have he : 0 ≤ ((((z 0).1 q : ℝ)/V)-(1/1358-eta))/
      Real.exp (1358*prefixElapsed K (Preorder.frestrictLe K z)) := by
    apply div_nonneg
    · rw [hinit]
      linarith
    · exact (Real.exp_pos _).le
  linarith only [hp,he]

end
end RandomViability

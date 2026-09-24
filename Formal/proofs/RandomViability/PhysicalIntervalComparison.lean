import proofs.RandomViability.PhysicalFoodStartup

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem compensated_scalar_interval_lower (x A d h : ℕ → ℝ) (a b eta s : ℝ) (K : ℕ)
    (ha : 0 < a) (hA0 : A 0 = 0) (hs : 0 ≤ s)
    (hh : ∀ i < K,0 ≤ h i)
    (hd : ∀ i ≤ K,b-a*x i ≤ d i)
    (hnoise : ∀ i < K,∀ u ∈ Icc 0 (h i),A i-d i*u ≤ eta)
    (hjump : ∀ i < K,x (i+1)-A (i+1) = x i-A i+d i*h i)
    (hlast : ∀ u ∈ Icc 0 s,A K-d K*u ≤ eta)
    (hend : -eta ≤ A K-d K*s) :
    (x 0-(b/a-eta))/Real.exp (a*((∑ i : Fin K,h i)+s))+b/a-2*eta ≤ x K := by
  let e := b/a-eta
  have hstep : ∀ i < K,((x i-A i)-e)/Real.exp (a*h i)+e ≤ x (i+1)-A (i+1) := by
    intro i hi
    rw [hjump i hi]
    exact compensated_holding_comparison (x i) (A i) (d i) a b eta (h i)
      ha (hh i hi) (hd i hi.le) (hnoise i hi)
  have hp := scalar_affine_recurrence_lower (fun i => x i-A i) h a e K hstep
  simp only [hA0,sub_zero] at hp
  have hl := compensated_holding_comparison (x K) (A K) (d K) a b eta s
    ha hs (hd K le_rfl) hlast
  have he : Real.exp (a*((∑ i : Fin K,h i)+s)) =
      Real.exp (a*(∑ i : Fin K,h i))*Real.exp (a*s) := by rw [mul_add,Real.exp_add]
  have hr : (x 0-e)/Real.exp (a*((∑ i : Fin K,h i)+s))+e ≤ x K-A K+d K*s := by
    calc
      _ = (((x 0-e)/Real.exp (a*(∑ i : Fin K,h i))+e)-e)/Real.exp (a*s)+e := by
        rw [he]
        field_simp
        ring
      _ ≤ ((x K-A K)-e)/Real.exp (a*s)+e := add_le_add
        (div_le_div_of_nonneg_right (sub_le_sub_right hp e) (Real.exp_pos _).le) le_rfl
      _ ≤ _ := hl
  dsimp only [e] at hr
  linarith only [hr,hend]

/-- A partial final clock is handled without adding another 2eta loss. -/
theorem physical_coordinate_interval_comparison {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T a b eta s : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (ha : 0 < a) (hs0 : 0 ≤ s)
    (hsh : s ≤ min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z)))
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hactive : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i < K,0 ≤ (z (i+1)).2.2)
    (hd : ∀ i ≤ K,b-a*(((z i).1 q : ℝ)/V) ≤ physicalCoordinateDrift c V basal cat (z i).1 q)
    (hnoise : ∀ i < K,∀ u ∈ Icc 0 (z (i+1)).2.2,
      coordinateCompensationWithinInterval c V basal cat q T z i u ≤ eta)
    (hfinal : ∀ u ∈ Icc 0 (min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z))),
      |coordinateCompensationWithinInterval c V basal cat q T z K u| ≤ eta) :
    ((((z 0).1 q : ℝ)/V)-(b/a-eta))/
      Real.exp (a*(prefixElapsed K (Preorder.frestrictLe K z)+s))+b/a-2*eta ≤ ((z K).1 q : ℝ)/V := by
  apply compensated_scalar_interval_lower
    (fun i => ((z i).1 q : ℝ)/V) (censoredCoordinatePrefix c V basal cat q T z)
    (fun i => physicalCoordinateDrift c V basal cat (z i).1 q) (fun i => (z (i+1)).2.2)
    a b eta s K ha
  · simp [censoredCoordinatePrefix]
  · exact hs0
  · exact hh
  · exact hd
  · intro i hi u hui
    simpa only [coordinateCompensationWithinInterval,if_neg (hactive i hi.le)] using hnoise i hi u hui
  · intro i hi
    exact coordinate_corrected_jump c V basal cat q T z i (hc i hi) (hactive i hi.le) (ht i hi)
  · intro u hu
    have hb := (abs_le.mp (hfinal u ⟨hu.1,hu.2.trans hsh⟩)).2
    simpa only [coordinateCompensationWithinInterval,if_neg (hactive K le_rfl)] using hb
  · have hb := (abs_le.mp (hfinal s ⟨hs0,hsh⟩)).1
    simpa only [coordinateCompensationWithinInterval,if_neg (hactive K le_rfl)] using hb

end
end RandomViability

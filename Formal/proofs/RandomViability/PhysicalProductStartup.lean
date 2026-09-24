import proofs.RandomViability.PhysicalIntervalComparison

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem physical_product_forced_drift {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (N : Molecule n → ℕ) (hM : (countMass N : ℝ) ≤ 11*V) (r : Reaction n)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (f : ℝ) (hf : 0 ≤ f)
    (hu : f ≤ (N (reactionLeft r) : ℝ)/V) (hw : f ≤ (N (reactionRight r) : ℝ)/V) :
    (1/500000000 : ℝ)*f^2-1476*((N (reactionProduct r) : ℝ)/V) ≤
      physicalCoordinateDrift c V basal cat N (reactionProduct r) := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hnf := (nonfoodMass_le_mass x hx).trans hm
  have hC : 4*(1/500000000 : ℝ)+(16/3)*nonfoodMass x ≤ 59 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hC (hx (reactionProduct r))
  have hpair := mul_le_mul hu hw hf (hx (reactionLeft r))
  have hforce := mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 1/500000000)
  have hregen : 0 ≤ x (reactionProduct r)*(4*x (reactionLeft r)*x (reactionRight r)) :=
    mul_nonneg (hx _) (mul_nonneg (mul_nonneg (by norm_num) (hx _)) (hx _))
  have hg := physical_product_drift_bound c V hV basal cat N (1/500000000) (by norm_num)
    hb hc hfood hM r hlen huw huz hwz hsel hbas hcat
  change (1/500000000 : ℝ)*x (reactionLeft r)*x (reactionRight r)+x (reactionProduct r)*
    (4*x (reactionLeft r)*x (reactionRight r)-1-25*(4*(1/500000000 : ℝ)+(16/3)*nonfoodMass x)) ≤ _ at hg
  change (1/500000000 : ℝ)*(f*f) ≤ (1/500000000)*(x (reactionLeft r)*x (reactionRight r)) at hforce
  change (1/500000000 : ℝ)*f^2-1476*x (reactionProduct r) ≤ _
  nlinarith only [hg,hmul,hforce,hregen]

theorem scalar_startup_after_one (a b eta t : ℝ) (ha : 0 < a)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (ht : 1 ≤ t) :
    b/(a+1)-2*eta ≤ -(b/a-eta)/Real.exp (a*t)+b/a-2*eta := by
  have hden : 0 < a+1 := by linarith
  have hE : a+1 ≤ Real.exp (a*t) := by
    have hm := mul_le_mul_of_nonneg_left ht ha.le
    have he := Real.add_one_le_exp (a*t)
    nlinarith only [hm,he]
  have hr := div_le_div_of_nonneg_left (div_nonneg hb ha.le) hden hE
  have heq : b/a-(b/a)/(a+1) = b/(a+1) := by field_simp; ring
  have hn : 0 ≤ eta/Real.exp (a*t) := div_nonneg heta (Real.exp_pos _).le
  rw [← heq]
  rw [neg_div,sub_div]
  linarith only [hr,hn]

/-- Conditional product startup at any physical time >=1 represented inside
an active holding interval. The food floors remain explicit hypotheses. -/
theorem physical_product_interval_floor {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅) (r : Reaction n)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (T s : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hinit : ((z 0).1 (reactionProduct r) : ℝ)/V = 0)
    (hs0 : 0 ≤ s)
    (hsh : s ≤ min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z)))
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hactive : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i < K,0 ≤ (z (i+1)).2.2)
    (hfoods : ∀ i ≤ K,
      (1/1358 : ℝ)-2/100000 ≤ ((z i).1 (reactionLeft r) : ℝ)/V ∧
      (1/1358 : ℝ)-2/100000 ≤ ((z i).1 (reactionRight r) : ℝ)/V)
    (hnoise : ∀ i < K,∀ u ∈ Icc 0 (z (i+1)).2.2,
      coordinateCompensationWithinInterval c V basal cat (reactionProduct r) T z i u ≤
        (1/300000000000000000000 : ℝ))
    (hfinal : ∀ u ∈ Icc 0 (min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z))),
      |coordinateCompensationWithinInterval c V basal cat (reactionProduct r) T z K u| ≤
        (1/300000000000000000000 : ℝ))
    (htime : 1 ≤ prefixElapsed K (Preorder.frestrictLe K z)+s) :
    (1/3000000000000000000 : ℝ) ≤ ((z K).1 (reactionProduct r) : ℝ)/V := by
  let b : ℝ := (1/500000000)*((1/1358)-2/100000)^2
  let eta : ℝ := 1/300000000000000000000
  have hd : ∀ i ≤ K,b-1476*(((z i).1 (reactionProduct r) : ℝ)/V) ≤
      physicalCoordinateDrift c V basal cat (z i).1 (reactionProduct r) := by
    intro i hi
    have hM : (countMass (z i).1 : ℝ) ≤ 11*V :=
      not_not.mp (not_or.mp (not_or.mp (hactive i hi)).2).1
    exact physical_product_forced_drift c V hV basal cat hb hcatCap hfood (z i).1 hM r
      hlen huw huz hwz hsel hbas hcat ((1/1358)-2/100000) (by norm_num)
      (hfoods i hi).1 (hfoods i hi).2
  have hp := physical_coordinate_interval_comparison c V basal cat (reactionProduct r) T
    1476 b eta s z K (by norm_num) hs0 hsh hc hactive ht hh hd hnoise hfinal
  rw [hinit,zero_sub] at hp
  have he := scalar_startup_after_one 1476 b eta
    (prefixElapsed K (Preorder.frestrictLe K z)+s) (by norm_num)
    (by dsimp [b]; positivity) (by dsimp [eta]; positivity) htime
  have hm : (1/3000000000000000000 : ℝ) ≤ b/(1476+1)-2*eta := by
    norm_num [b,eta]
  exact (hm.trans he).trans hp

end
end RandomViability

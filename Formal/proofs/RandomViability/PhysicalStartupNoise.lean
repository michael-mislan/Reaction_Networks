import proofs.RandomViability.PhysicalProductStartup

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

def coordinateNoiseBound {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T eta : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∀ k u,0 ≤ u → u ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) →
    |coordinateCompensationWithinInterval c V basal cat q T z k u| ≤ eta

theorem physical_food_floor_from_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (q : Molecule n) (hq : molLength q = 2) (T eta : ℝ) (heta : 0 ≤ eta)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hinit : ((z 0).1 q : ℝ)/V = 1)
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hs : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i ≤ K,0 ≤ (z (i+1)).2.2)
    (hnoise : coordinateNoiseBound c V basal cat q T eta z) :
    (1/1358 : ℝ)-2*eta ≤ ((z K).1 q : ℝ)/V := by
  apply physical_food_prefix_floor c V hV basal cat hb hcat hfood q hq T eta heta z K hinit
    hc (fun i hi => hs i hi.le) ht (fun i hi => hh i hi.le)
  · intro i hi u hu
    exact (abs_le.mp (hnoise i u hu.1 (le_min hu.2 (hu.2.trans (ht i hi))))).2
  · have hrem : 0 ≤ T-prefixElapsed K (Preorder.frestrictLe K z) :=
      sub_nonneg.mpr (le_of_not_ge (not_or.mp (not_or.mp (hs K le_rfl)).2).2)
    have he := (abs_le.mp (hnoise K 0 le_rfl (le_min (hh K le_rfl) hrem))).1
    simpa only [coordinateCompensationWithinInterval,if_neg (hs K le_rfl),mul_zero,sub_zero] using he

/-- Combined literal-path startup: both food floors are proved from their
noise bounds, rather than assumed independently in the product comparison. -/
theorem physical_startup_product_from_noise {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ)) (hcatCap : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : (1/500000000 : ℝ) ≤ basal r) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (T s : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (K : ℕ)
    (hinitL : ((z 0).1 (reactionLeft r) : ℝ)/V = 1)
    (hinitR : ((z 0).1 (reactionRight r) : ℝ)/V = 1)
    (hinit : ((z 0).1 (reactionProduct r) : ℝ)/V = 0)
    (hs0 : 0 ≤ s)
    (hsh : s ≤ min (z (K+1)).2.2 (T-prefixElapsed K (Preorder.frestrictLe K z)))
    (hc : ∀ i < K,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hactive : ∀ i ≤ K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z))
    (ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z))
    (hh : ∀ i ≤ K,0 ≤ (z (i+1)).2.2)
    (hnoiseL : coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z)
    (hnoiseR : coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z)
    (hnoiseP : coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z)
    (htime : 1 ≤ prefixElapsed K (Preorder.frestrictLe K z)+s) :
    (1/3000000000000000000 : ℝ) ≤ ((z K).1 (reactionProduct r) : ℝ)/V := by
  apply physical_product_interval_floor c V hV basal cat hb hcatCap hfood r hlen huw huz hwz
    hsel hbas hcat T s z K hinit hs0 hsh hc hactive ht (fun i hi => hh i hi.le)
  · intro i hi
    have hf (q : Molecule n) (hq : molLength q = 2) (hqi : ((z 0).1 q : ℝ)/V = 1)
        (hnq : coordinateNoiseBound c V basal cat q T (1/100000) z) :
        (1/1358 : ℝ)-2/100000 ≤ ((z i).1 q : ℝ)/V := by
      have hv := physical_food_floor_from_noise c V hV basal cat hb hcatCap hfood q hq
        T (1/100000) (by norm_num) z i hqi
        (fun j hj => hc j (lt_of_lt_of_le hj hi))
        (fun j hj => hactive j (hj.trans hi))
        (fun j hj => ht j (lt_of_lt_of_le hj hi))
        (fun j hj => hh j (hj.trans hi)) hnq
      convert hv using 1
      ring
    exact ⟨hf _ hl hinitL hnoiseL,hf _ hr hinitR hnoiseR⟩
  · intro i hi u hu
    exact (abs_le.mp (hnoiseP i u hu.1 (le_min hu.2 (hu.2.trans (ht i hi))))).2
  · intro u hu
    exact hnoiseP K u hu.1 hu.2
  · exact htime

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- The noise condition used by startup has an actual-law upper-measure bound. -/
theorem physical_noise_bound_failure (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (δ T eta : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T)
    (hmargin : δ+2/V ≤ eta) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | ¬coordinateNoiseBound c V basal cat q T eta z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(96000*T+2*δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_coordinate_interval_tail hn c V hV basal cat N hbasal hcat q δ T hδ hT)
  intro z hz
  simp only [coordinateNoiseBound] at hz
  push Not at hz
  obtain ⟨k,u,h0,hu,hlarge⟩ := hz
  exact ⟨k,u,h0,hu,hmargin.trans hlarge.le⟩

end
end RandomViability

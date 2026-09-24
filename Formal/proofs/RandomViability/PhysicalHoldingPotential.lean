import proofs.RandomViability.PhysicalStartupProbability
import proofs.RandomViability.CompensatedPotentialInterval

namespace RandomViability
open Classical Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

def correctedCoordinate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  ((z k).1 q : ℝ)/V-censoredCoordinatePrefix c V basal cat q T z k+
    physicalCoordinateDrift c V basal cat (z k).1 q*s

def correctedPotential {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ) (s : ℝ) : ℝ :=
  collectivePotential (correctedCoordinate c V basal cat (reactionLeft r) T z k s)
    (correctedCoordinate c V basal cat (reactionRight r) T z k s)
    (correctedCoordinate c V basal cat (reactionProduct r) T z k s)

theorem corrected_coordinate_link {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ)
    (hc : jumpConsistent unboundedPhysicalNext (z k).1 (z (k+1)))
    (hs : ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z))
    (ht : (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z)) :
    correctedCoordinate c V basal cat q T z k (z (k+1)).2.2 =
      correctedCoordinate c V basal cat q T z (k+1) 0 := by
  simpa only [correctedCoordinate,mul_zero,add_zero] using
    (coordinate_corrected_jump c V basal cat q T z k hc hs ht).symm

theorem corrected_potential_link {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (r : Reaction n) (T : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (k : ℕ)
    (hc : jumpConsistent unboundedPhysicalNext (z k).1 (z (k+1)))
    (hs : ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z))
    (ht : (z (k+1)).2.2 ≤ T-prefixElapsed k (Preorder.frestrictLe k z)) :
    correctedPotential c V basal cat r T z k (z (k+1)).2.2 =
      correctedPotential c V basal cat r T z (k+1) 0 := by
  unfold correctedPotential
  rw [corrected_coordinate_link c V basal cat _ T z k hc hs ht,
    corrected_coordinate_link c V basal cat _ T z k hc hs ht,
    corrected_coordinate_link c V basal cat _ T z k hc hs ht]

theorem physical_holding_potential_gain {n : ℕ}
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*eps) (hcatCap : ∀ r q,(cat r q : ℝ) ≤ 16)
    (hfood : ∀ q,molLength q ≤ 2 → c q = ∅) (r : Reaction n)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : eps ≤ (basal r : ℝ)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ))
    (T : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hlimit : b ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)))
    (hactive : ¬censoredNonfoodStop V T (massExitStop V) k (Preorder.frestrictLe k z))
    (hM : (countMass (z k).1 : ℝ) ≤ 11*V)
    (hfloor : (1/3000000000000000000 : ℝ) ≤ ((z k).1 (reactionProduct r) : ℝ)/V)
    (hnoiseL : coordinateNoiseBound c V basal cat (reactionLeft r) T (1/100000) z)
    (hnoiseR : coordinateNoiseBound c V basal cat (reactionRight r) T (1/100000) z)
    (hnoiseP : coordinateNoiseBound c V basal cat (reactionProduct r) T (1/300000000000000000000) z) :
    (b-a)*((19/10 : ℝ)-480*eps-640*nonfoodMass (fun q => ((z k).1 q : ℝ)/V)) ≤
      correctedPotential c V basal cat r T z k b-correctedPotential c V basal cat r T z k a := by
  let x : Molecule n → ℝ := fun q => ((z k).1 q : ℝ)/V
  let A := fun q => censoredCoordinatePrefix c V basal cat q T z k
  let d := physicalCoordinateDrift c V basal cat (z k).1
  let C := 4*eps+(16/3)*nonfoodMass x
  have hpos : ∀ q,0 ≤ x q := fun q => by dsimp [x]; positivity
  have hx : 0 < x (reactionProduct r) := by dsimp [x]; linarith only [hfloor]
  have hnf : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro q _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL := physical_food_drift_bound c V hV basal cat (z k).1 eps heps hb hcatCap hfood hM _ hl
  have hR := physical_food_drift_bound c V hV basal cat (z k).1 eps heps hb hcatCap hfood hM _ hr
  have hP := physical_product_drift_bound c V hV basal cat (z k).1 eps heps hb hcatCap hfood hM r
    hlen huw huz hwz hsel hbas hcat
  have hdP : x (reactionProduct r)*(4*x (reactionLeft r)*x (reactionRight r)-1-25*C) ≤
      d (reactionProduct r) := by
    have hh : 0 ≤ eps*x (reactionLeft r)*x (reactionRight r) := by positivity
    change eps*x (reactionLeft r)*x (reactionRight r)+
      x (reactionProduct r)*(4*x (reactionLeft r)*x (reactionRight r)-1-25*C) ≤ _ at hP
    linarith only [hP,hh]
  have hnoise (q : Molecule n) (η : ℝ) (hn : coordinateNoiseBound c V basal cat q T η z) :
      ∀ s ∈ Icc a b,|A q-d q*s| ≤ η := by
    intro s hs
    have hh := hn k s (ha.trans hs.1) (hs.2.trans hlimit)
    simpa only [coordinateCompensationWithinInterval,if_neg hactive] using hh
  have hg := compensated_holding_potential_gain (x (reactionLeft r)) (x (reactionRight r))
    (x (reactionProduct r)) (A (reactionLeft r)) (A (reactionRight r)) (A (reactionProduct r))
    (d (reactionLeft r)) (d (reactionRight r)) (d (reactionProduct r)) C a b
    (hpos _) (hpos _) hx hC hab hL hR hdP
    (hnoise _ _ hnoiseL) (hnoise _ _ hnoiseR)
    (by
      intro s hs
      have hh := hnoise _ _ hnoiseP s hs
      dsimp [x]
      linarith only [hh,hfloor])
  have he : (19/10 : ℝ)-480*eps-640*nonfoodMass x = (19/10 : ℝ)-120*C := by dsimp [C]; ring
  change (b-a)*((19/10 : ℝ)-480*eps-640*nonfoodMass x) ≤ _
  rw [he]
  exact hg

end
end RandomViability

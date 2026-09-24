import proofs.RandomViability.BoundedCumulativeReward
import proofs.RandomViability.PoissonRewardPaths

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def positiveCatalyticReward {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) : ℝ :=
  match ch with
  | .inr (.inr _) => max 0 (countNonfoodMass (boundedCountsValue
      ((boundedPhysicalCountModel c V D basal catalytic).next N ch)) - countNonfoodMass (boundedCountsValue N))
  | _ => 0

theorem positiveCatalyticReward_nonneg {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n) :
    0 ≤ positiveCatalyticReward c V D basal catalytic N ch := by
  rcases ch with (ch | ch) <;> cases ch <;> simp only [positiveCatalyticReward] <;> positivity

theorem positiveCatalyticReward_intensity {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    (∑ ch, (boundedPhysicalCountModel c V D basal catalytic).rate N ch *
      positiveCatalyticReward c V D basal catalytic N ch) = boundedCatalyticUptake c V D basal catalytic N := by
  simp only [Fintype.sum_sum_type, positiveCatalyticReward, mul_zero, Finset.sum_const_zero, zero_add]
  simp only [Fintype.sum_prod_type]
  rw [boundedCatalyticUptake_eq_actual_positive]
  exact Finset.sum_comm

def boundedUptakeTail {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (q : NNReal) (hq : 0 < (q : ℝ))
    (hbound : ∀ X : BoundedCounts n B, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q)
    (N : BoundedCounts n B) (t : NNReal) (s : ℝ) : ℝ :=
  (labeledUniformize (boundedPhysicalCountModel c V D basal catalytic) q hq hbound).poissonPathTail
    (liftChannelReward (positiveCatalyticReward c V D basal catalytic)) (q*t) N s

theorem bounded_uptake_tail_bound {n B k : ℕ} (hn : 2 ≤ n) (hk : 0 < k)
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ ShortIncidence k c)
    (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (κ : ℝ) (hκ : 0 ≤ κ) (hrate : ∀ r z, (catalytic r z : ℝ) ≤ κ)
    (q : NNReal) (hq : 0 < (q : ℝ)) (hqD : (D : ℝ) ≤ 2*q)
    (hbound : ∀ X : BoundedCounts n B, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q)
    (N : BoundedCounts n B) (hinit : ((boundedMass N : ℝ)/V)^3 ≤ 38000)
    (t : NNReal) (ht : 0 < (t : ℝ)) (j : ℝ) (hj : 0 < j) :
    boundedUptakeTail c V D basal catalytic q hq hbound N t (j*V*t) ≤ 152000*κ/((k : ℝ)*j) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hVp : 0 < (V : ℝ) := by linarith
  have havg : ∀ X : BoundedCounts n B, boundedCatalyticUptake c V D basal catalytic X / q ≤
      (4*κ*V/((k : ℝ)*q))*((boundedMass X : ℝ)/V)^3 := by
    intro X
    have hi := boundedCatalyticUptake_mass_bound c hgood V D hVp basal catalytic X κ hκ hrate
    calc
      _ = ((k : ℝ)*boundedCatalyticUptake c V D basal catalytic X)/((k : ℝ)*q) := by field_simp
      _ ≤ (4*κ*V*((boundedMass X : ℝ)/V)^3)/((k : ℝ)*q) :=
        div_le_div_of_nonneg_right hi (by positivity)
      _ = _ := by ring
  have he : (fun X : BoundedCounts n B =>
      (∑ ch, (boundedPhysicalCountModel c V D basal catalytic).rate X ch *
        positiveCatalyticReward c V D basal catalytic X ch)/(q : ℝ)) =
      (fun X => boundedCatalyticUptake c V D basal catalytic X / q) := by
    funext X
    rw [positiveCatalyticReward_intensity]
  have hpath : ∀ m : ℕ,
      (labeledUniformize (boundedPhysicalCountModel c V D basal catalytic) q hq hbound).pathExpectation
        (liftChannelReward (positiveCatalyticReward c V D basal catalytic)) m N ≤
        (m : ℝ)*(152000*κ*V/((k : ℝ)*q)) := by
    intro m
    rw [jump_pathExpectation_eq_kernel, he]
    have hh := kernel_accumulated_reward_bound
      ((boundedPhysicalCountModel c V D basal catalytic).uniformize q hq hbound)
      (fun X => ((boundedMass X : ℝ)/V)^3)
      (fun X => boundedCatalyticUptake c V D basal catalytic X / q)
      (1-(D : ℝ)/(2*q)) 38000 (4*κ*V/((k : ℝ)*q))
      (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hqD)) (by positivity)
      (fun X => bounded_cubic_uniformize_step hn c V D hV basal catalytic q hq hbound X) havg N hinit m
    calc
      _ ≤ (m : ℝ)*(4*κ*V/((k : ℝ)*q))*38000 := hh
      _ = _ := by ring
  have hg : ∀ (X : BoundedCounts n B) b, 0 ≤ liftChannelReward (positiveCatalyticReward c V D basal catalytic) X b := by
    intro X b
    cases b with
    | none => exact le_refl 0
    | some b => exact positiveCatalyticReward_nonneg c V D basal catalytic X b
  have hh := (labeledUniformize (boundedPhysicalCountModel c V D basal catalytic) q hq hbound).poissonPathTail_le
    _ hg (q*t) N (j*V*t) (152000*κ*V/((k : ℝ)*q)) (by positivity) hpath
  calc
    _ ≤ ((q*t : NNReal) : ℝ)*(152000*κ*V/((k : ℝ)*q))/(j*V*t) := hh
    _ = _ := by
      simp only [NNReal.coe_mul]
      field_simp

end
end RandomViability




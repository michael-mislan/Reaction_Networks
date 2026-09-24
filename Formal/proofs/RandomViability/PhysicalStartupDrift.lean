import proofs.RandomViability.PhysicalCoordinateDrift
import proofs.RandomViability.PhysicalSelectedFlux

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

theorem normalized_count_mass {n : ℕ} (N : Molecule n → ℕ) (V : NNReal) :
    polymerMass (fun z => (N z : ℝ)/V) = (countMass N : ℝ)/V := by
  simp [polymerMass,countMass,Finset.sum_div,mul_div_assoc]

theorem physical_food_drift_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*eps) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (q : Molecule n) (hq : molLength q = 2) :
    1-(N q : ℝ)/V-23*(4*eps+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V))*((N q : ℝ)/V) ≤
      physicalCoordinateDrift c V basal cat N q := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let C : ℝ := 4*eps+(16/3)*nonfoodMass x
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hnf : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hl := collective_loss_bound (fun _ => C) x hx C hC (fun _ => le_rfl) q
  have hlen : (molLength q : ℝ) = 2 := by exact_mod_cast hq
  rw [hlen] at hl
  have hh := physical_coordinate_drift_lower c V hV basal cat N C
    (physical_pair_flux_nonfood_bound c V hV basal cat N eps hb hc hfood) q
  rw [if_pos (by omega)] at hh
  have hm' := mul_le_mul_of_nonneg_right hm (mul_nonneg hC (hx q))
  change 1-x q-23*C*x q ≤ _
  change 1-x q-collectiveLoss (fun _ => C) x q ≤ _ at hh
  nlinarith only [hl,hh,hm']

theorem physical_product_gain_minus_loss {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (C : ℝ)
    (hflux : ∀ r d,physicalPairFlux c V basal cat N r d ≤ C*
      (if d then ((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)
       else (N (reactionProduct r) : ℝ)/V)) (r₀ : Reaction n)
    (hq : 2 < molLength (reactionProduct r₀)) :
    physicalPairFlux c V basal cat N r₀ true-(N (reactionProduct r₀) : ℝ)/V-
      collectiveLoss (fun _ => C) (fun z => (N z : ℝ)/V) (reactionProduct r₀) ≤
      physicalCoordinateDrift c V basal cat N (reactionProduct r₀) := by
  let q := reactionProduct r₀
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let F := fun r => physicalPairFlux c V basal cat N r true
  let B := fun r => physicalPairFlux c V basal cat N r false
  have hs : (∑ r, ((if reactionProduct r = q then F r else 0)-
      ((if reactionLeft r = q then C*x (reactionLeft r)*x (reactionRight r) else 0)+
       (if reactionRight r = q then C*x (reactionLeft r)*x (reactionRight r) else 0)+
       (if reactionProduct r = q then C*x (reactionProduct r) else 0)))) ≤
      ∑ r,(F r-B r)*reactionCoordinateChange r q := by
    apply Finset.sum_le_sum
    intro r _
    have hF : F r ≤ C*(x (reactionLeft r)*x (reactionRight r)) := hflux r true
    have hB : B r ≤ C*x (reactionProduct r) := hflux r false
    have hF0 : 0 ≤ F r := physical_pair_flux_nonneg c V basal cat N r true
    have hB0 : 0 ≤ B r := physical_pair_flux_nonneg c V basal cat N r false
    unfold reactionCoordinateChange singleCount
    simp only [eq_comm (a := q)]
    split_ifs <;> norm_num <;> nlinarith only [hF,hB,hF0,hB0]
  have he : (∑ r, ((if reactionProduct r = q then F r else 0)-
      ((if reactionLeft r = q then C*x (reactionLeft r)*x (reactionRight r) else 0)+
       (if reactionRight r = q then C*x (reactionLeft r)*x (reactionRight r) else 0)+
       (if reactionProduct r = q then C*x (reactionProduct r) else 0)))) =
      (∑ r,if reactionProduct r = q then F r else 0)-collectiveLoss (fun _ => C) x q := by
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,collectiveLoss]
  rw [he] at hs
  have hg : F r₀ ≤ ∑ r,if reactionProduct r = q then F r else 0 := by
    calc
      _ = (if reactionProduct r₀ = q then F r₀ else 0) := by rw [if_pos rfl]
      _ ≤ _ := Finset.single_le_sum (f := fun r => if reactionProduct r = q then F r else 0)
        (fun r _ => by
          dsimp only
          split_ifs
          · exact physical_pair_flux_nonneg c V basal cat N r true
          · exact le_rfl)
        (Finset.mem_univ r₀)
  rw [physical_coordinate_drift_decomposition c V hV basal cat N (reactionProduct r₀),if_neg (by omega)]
  change F r₀-x q-collectiveLoss (fun _ => C) x q ≤ 0-x q+∑ r,(F r-B r)*reactionCoordinateChange r q
  linarith only [hs,hg]

theorem physical_product_drift_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*eps) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅)
    (hM : (countMass N : ℝ) ≤ 11*V) (r : Reaction n)
    (hlen : molLength (reactionProduct r) = 4)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r))
    (hbas : eps ≤ (basal r : ℝ)) (hcat : 4 ≤ (cat r (reactionProduct r) : ℝ)) :
    eps*((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)+
      ((N (reactionProduct r) : ℝ)/V)*
      (4*((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)-1-
        25*(4*eps+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V))) ≤
      physicalCoordinateDrift c V basal cat N (reactionProduct r) := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let C : ℝ := 4*eps+(16/3)*nonfoodMass x
  have hx : ∀ z,0 ≤ x z := fun z => by dsimp [x]; positivity
  have hnf : 0 ≤ nonfoodMass x := by
    apply Finset.sum_nonneg
    intro z _
    split_ifs <;> positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : polymerMass x ≤ 11 := by
    rw [normalized_count_mass]
    exact (div_le_iff₀ hV).mpr hM
  have hl := collective_loss_bound (fun _ => C) x hx C hC (fun _ => le_rfl) (reactionProduct r)
  have hlen' : (molLength (reactionProduct r) : ℝ) = 4 := by exact_mod_cast hlen
  rw [hlen'] at hl
  have hh := physical_product_gain_minus_loss c V hV basal cat N C
    (physical_pair_flux_nonfood_bound c V hV basal cat N eps hb hc hfood) r (by omega)
  have hg := physical_selected_flux_lower c V hV basal cat N r huw huz hwz hsel eps hbas hcat
  have hm' := mul_le_mul_of_nonneg_right hm (mul_nonneg hC (hx (reactionProduct r)))
  change eps*x (reactionLeft r)*x (reactionRight r)+x (reactionProduct r)*
    (4*x (reactionLeft r)*x (reactionRight r)-1-25*C) ≤ _
  change physicalPairFlux c V basal cat N r true-x (reactionProduct r)-
    collectiveLoss (fun _ => C) x (reactionProduct r) ≤ _ at hh
  change (eps+4*x (reactionProduct r))*x (reactionLeft r)*x (reactionRight r) ≤ _ at hg
  nlinarith only [hl,hh,hg,hm']

end
end RandomViability

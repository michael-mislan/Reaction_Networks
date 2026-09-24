import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability
import proofs.PowerLawSmallRAF.SourceCriticalSecondMoment
import proofs.HordijkSteelThreshold.SourceTerminalRAF

namespace RandomViability
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def FoodIgnition {n : ℕ} (c : SourceMoleculeFibreConfig n) : Prop :=
  ∃ x ∈ binaryFood n 2, ∃ r : Reaction n,
    RevSeedReaction (binaryPolymerCRS n 2) r ∧ r ∈ c x

def eventMass (a : ℝ) (n : ℕ) (E : SourceMoleculeFibreConfig n → Prop) : ℝ :=
  ∑ c, if E c then sourcePowerLawConfigWeight a n c else 0

theorem eventMass_nonneg (a : ℝ) (n : ℕ) (ha : 1 < a)
    (E : SourceMoleculeFibreConfig n → Prop) : 0 ≤ eventMass a n E := by
  apply Finset.sum_nonneg
  intro c _
  split_ifs
  · exact sourcePowerLawConfigWeight_nonneg a n ha c
  · exact le_rfl

theorem eventMass_mono (a : ℝ) (n : ℕ) (ha : 1 < a)
    {E F : SourceMoleculeFibreConfig n → Prop} (h : ∀ c, E c → F c) :
    eventMass a n E ≤ eventMass a n F := by
  apply Finset.sum_le_sum
  intro c _
  by_cases he : E c
  · simp [he, h c he]
  · simp only [if_neg he]
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg a n ha c
    · exact le_rfl

theorem finite_union_mass_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (E : I → Ω → Prop) :
    (∑ z, if ∃ i, E i z then w z else 0) ≤
      ∑ i, ∑ z, if E i z then w z else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  by_cases h : ∃ i, E i z
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    calc
      w z = (if E i z then w z else 0) := (if_pos hi).symm
      _ ≤ ∑ j, if E j z then w z else 0 :=
        Finset.single_le_sum (f := fun j => if E j z then w z else 0)
          (fun j _ => by dsimp only; split_ifs <;> first | exact hw z | exact le_rfl)
          (Finset.mem_univ i)
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hw z | exact le_rfl)

/-- A conservative 408-incidence bound avoids any independent-edge replacement.
The sharper count of genuinely nonfood-producing food channels is 192. -/
theorem foodIgnition_mass_le (a : ℝ) (n : ℕ) (ha : 1 < a) (hn : 4 ≤ n) :
    eventMass a n FoodIgnition ≤
      408 * (windowZipfMean a (sourceReactionCount n) / sourceReactionCount n) := by
  letI : Fintype (SourceMoleculeFibreConfig n) := inferInstance
  let I := ↥(binaryFood n 2) × PolymerSeedReaction n 2
  let E : I → SourceMoleculeFibreConfig n → Prop := fun i c => i.2.val ∈ c i.1.val
  have he : ∀ c, FoodIgnition c ↔ ∃ i : I, E i c := by
    intro c
    constructor
    · rintro ⟨x, hx, r, hr, hc⟩
      exact ⟨(⟨x,hx⟩,⟨r,hr⟩),hc⟩
    · rintro ⟨⟨x,r⟩,hc⟩
      exact ⟨x.val,x.property,r.val,r.property,hc⟩
  have hc : Fintype.card I ≤ 408 := by
    have hf : (binaryFood n 2).card ≤ 6 := by
      simpa only [show Fintype.card (Molecule 2) = 6 from by decide] using
        HordijkSteelThreshold.binaryFood_card_le_cutoff n 2
    dsimp [I]
    rw [Fintype.card_prod, Fintype.card_coe]
    exact (Nat.mul_le_mul hf (card_polymerSeedReaction_le_68 n)).trans (by norm_num)
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hm0 : 0 ≤ windowZipfMean a (sourceReactionCount n) := by
    rw [windowZipfMean, windowDirectNumerator]
    apply div_nonneg _ hzpos.le
    exact add_nonneg
      (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (cappedRpowTail_nonneg a _)
  have hm : 0 ≤ windowZipfMean a (sourceReactionCount n) / sourceReactionCount n :=
    div_nonneg hm0 (Nat.cast_nonneg _)
  change (∑ c : SourceMoleculeFibreConfig n, if FoodIgnition c then sourcePowerLawConfigWeight a n c else 0) ≤ _
  have heq : (∑ c : SourceMoleculeFibreConfig n, if FoodIgnition c then sourcePowerLawConfigWeight a n c else 0) =
      ∑ c : SourceMoleculeFibreConfig n, if ∃ i : I, E i c then sourcePowerLawConfigWeight a n c else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : FoodIgnition c
    · rw [if_pos h, if_pos ((he c).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((he c).mpr hh))]
  rw [heq]
  calc
    _ ≤ ∑ i : I, ∑ c : SourceMoleculeFibreConfig n, if E i c then sourcePowerLawConfigWeight a n c else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro c _
      by_cases h : ∃ i : I, E i c
      · obtain ⟨i,hi⟩ := h
        rw [if_pos ⟨i,hi⟩]
        have hs := Finset.single_le_sum
          (f := fun j : I => if E j c then sourcePowerLawConfigWeight a n c else 0)
          (s := Finset.univ)
          (fun j _ => by dsimp only; split_ifs <;> first | exact sourcePowerLawConfigWeight_nonneg a n ha c | exact le_rfl)
          (Finset.mem_univ i)
        simpa only [if_pos hi] using hs
      · rw [if_neg h]
        exact Finset.sum_nonneg (fun j _ => by split_ifs <;> first | exact sourcePowerLawConfigWeight_nonneg a n ha c | exact le_rfl)
    _ ≤ ∑ _i : I, windowZipfMean a (sourceReactionCount n) / sourceReactionCount n := by
      apply Finset.sum_le_sum
      intro i _
      exact source_single_incidence_mass_le_mean_div a ha hn i.1.val i.2.val
    _ = (Fintype.card I : ℝ) * (windowZipfMean a (sourceReactionCount n) /
        sourceReactionCount n) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hm

theorem critical_incidence_tendsto_zero :
    Tendsto (fun n : ℕ => windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n) /
      sourceReactionCount n) atTop (𝓝 0) := by
  have hx := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
    sourceMoleculeCount_tendsto_atTop).inv_tendsto_atTop
  have ht := sourceExactCriticalFirstMoment_scaled_tendsto.mul hx
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  dsimp only [Pi.inv_apply, Function.comp_apply]
  field_simp

theorem foodIgnition_mass_tendsto_zero :
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n FoodIgnition) atTop (𝓝 0) := by
  have hu := critical_incidence_tendsto_zero.const_mul 408
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n ha
    exact eventMass_nonneg _ n ha _
  · filter_upwards [eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact foodIgnition_mass_le _ n ha hn

end
end RandomViability

import proofs.RandomViability.Startup

namespace RandomViability
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section

def ShortProductReaction (n L : ℕ) := {r : Reaction n // reactionProductLength r ≤ L}

instance (n L : ℕ) : Fintype (ShortProductReaction n L) := inferInstanceAs
  (Fintype {r : Reaction n // reactionProductLength r ≤ L})

theorem shortProductReaction_card_le (n L : ℕ) :
    Fintype.card (ShortProductReaction n L) ≤ Fintype.card (Reaction L) := by
  let f : ShortProductReaction n L → Reaction L := fun r =>
    ⟨⟨r.val.1.val, by have h := r.property; dsimp [reactionProductLength] at h; omega⟩,
      r.val.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨ai,aw⟩,ha⟩ ⟨⟨bi,bw⟩,hb⟩ h
    apply Subtype.ext
    have hi : ai = bi := Fin.ext (congrArg (fun z : Reaction L => z.1.val) h)
    subst bi
    have hw : aw.1 = bw.1 := Fin.ext (congrArg (fun z : Reaction L => z.2.1.val) h)
    have hs : aw.2 = bw.2 := Fin.ext (congrArg (fun z : Reaction L => z.2.2.val) h)
    have hp : aw = bw := Prod.ext hw hs
    subst bw
    rfl
  exact Fintype.card_le_of_injective f hf

def ShortIncidence {n : ℕ} (k : ℕ) (c : SourceMoleculeFibreConfig n) : Prop :=
  ∃ x ∈ binaryFood n k, ∃ r : Reaction n,
    reactionProductLength r ≤ k + 2 ∧ r ∈ c x

theorem shortIncidence_mass_le (a : ℝ) (n k : ℕ) (ha : 1 < a) (hn : 4 ≤ n) :
    eventMass a n (ShortIncidence k) ≤
      (Fintype.card (Molecule k) * Fintype.card (Reaction (k+2)) : ℕ) *
        (windowZipfMean a (sourceReactionCount n) / sourceReactionCount n) := by
  letI : Fintype (SourceMoleculeFibreConfig n) := inferInstance
  let I := ↥(binaryFood n k) × ShortProductReaction n (k+2)
  let E : I → SourceMoleculeFibreConfig n → Prop := fun i c => i.2.val ∈ c i.1.val
  have he : ∀ c, ShortIncidence k c ↔ ∃ i : I, E i c := by
    intro c
    constructor
    · rintro ⟨x,hx,r,hr,hc⟩
      exact ⟨(⟨x,hx⟩,⟨r,hr⟩),hc⟩
    · rintro ⟨⟨x,r⟩,hc⟩
      exact ⟨x.val,x.property,r.val,r.property,hc⟩
  have hc : Fintype.card I ≤ Fintype.card (Molecule k) * Fintype.card (Reaction (k+2)) := by
    dsimp [I]
    rw [Fintype.card_prod, Fintype.card_coe]
    exact Nat.mul_le_mul (HordijkSteelThreshold.binaryFood_card_le_cutoff n k)
      (shortProductReaction_card_le n (k+2))
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
  change (∑ c : SourceMoleculeFibreConfig n, if ShortIncidence k c then sourcePowerLawConfigWeight a n c else 0) ≤ _
  have heq : (∑ c : SourceMoleculeFibreConfig n, if ShortIncidence k c then sourcePowerLawConfigWeight a n c else 0) =
      ∑ c : SourceMoleculeFibreConfig n, if ∃ i : I, E i c then sourcePowerLawConfigWeight a n c else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : ShortIncidence k c
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

theorem shortIncidence_mass_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n (ShortIncidence k)) atTop (𝓝 0) := by
  have hu := critical_incidence_tendsto_zero.const_mul
    ((Fintype.card (Molecule k) * Fintype.card (Reaction (k+2)) : ℕ) : ℝ)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n ha
    exact eventMass_nonneg _ n ha _
  · filter_upwards [eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact shortIncidence_mass_le _ n k ha hn

theorem shortIncidence_free_left_food {n k : ℕ} {c : SourceMoleculeFibreConfig n}
    (hgood : ¬ ShortIncidence k c) (r : Reaction n) (x : Molecule n)
    (hselect : r ∈ c x) (hfood : molLength (reactionLeft r) ≤ 2) :
    k < molLength x ∨ k < molLength (reactionRight r) := by
  by_contra h
  push Not at h
  apply hgood
  refine ⟨x, ?_, r, ?_, hselect⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩
  · have hlen := reaction_length_add r
    simp only [molLength_reactionLeft, molLength_reactionRight] at hfood h
    omega

theorem shortIncidence_free_right_food {n k : ℕ} {c : SourceMoleculeFibreConfig n}
    (hgood : ¬ ShortIncidence k c) (r : Reaction n) (x : Molecule n)
    (hselect : r ∈ c x) (hfood : molLength (reactionRight r) ≤ 2) :
    k < molLength x ∨ k < molLength (reactionLeft r) := by
  by_contra h
  push Not at h
  apply hgood
  refine ⟨x, ?_, r, ?_, hselect⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩
  · have hlen := reaction_length_add r
    simp only [molLength_reactionLeft, molLength_reactionRight] at hfood h
    omega

end
end RandomViability

import proofs.RandomViability.BoundedCountModel
import proofs.RandomViability.MassMoment

namespace RandomViability
open Classical RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

def boundedMass {n B : ℕ} (N : BoundedCounts n B) : ℕ := countMass (boundedCountsValue N)

/-- Balanced channels preserve actual finite-model mass, including the
disabled-channel and cutoff branches of the transition definition. -/
theorem boundedPhysical_mass_next_of_balance {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n)
    (hb : countMass (physicalChannelInput ch) = countMass (physicalChannelOutput ch)) :
    boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N ch) = boundedMass N := by
  unfold boundedPhysicalCountModel
  dsimp only
  split_ifs with h
  · unfold boundedMass
    rw [truncateCounts_internal_unchanged N _ _ h hb]
    exact applyCountChannel_mass _ _ _ h hb
  · rfl

theorem bounded_internal_cubic_contribution_zero {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (ch : PhysicalCountChannel n)
    (hb : countMass (physicalChannelInput ch) = countMass (physicalChannelOutput ch)) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N ch *
      (((boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N ch) : ℝ) / V)^3 -
      ((boundedMass N : ℝ) / V)^3) = 0 := by
  rw [boundedPhysical_mass_next_of_balance c V D basal catalytic N ch hb]
  ring

/-- Every internal term in the actual generator vanishes. -/
theorem bounded_internal_cubic_sum_zero {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    (∑ ch : (Reaction n × Bool) ⊕ (Reaction n × Molecule n × Bool),
      (boundedPhysicalCountModel c V D basal catalytic).rate N (.inr ch) *
        (((boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inr ch)) : ℝ) / V)^3 -
        ((boundedMass N : ℝ) / V)^3)) = 0 := by
  apply Finset.sum_eq_zero
  intro ch _
  apply bounded_internal_cubic_contribution_zero
  cases ch with
  | inl ch => exact physical_basal_channel_balanced ch.1 ch.2
  | inr ch => exact physical_catalytic_channel_balanced ch.1 ch.2.1 ch.2.2

theorem bounded_food_rate {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (f : ↥(binaryFood n 2)) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inl (.inl f)) = (D : ℝ)*V := by
  simp [boundedPhysicalCountModel, physicalChannelInput, physicalChannelRate, physicalChannelCoefficient]

theorem truncated_mass_upper {n B : ℕ} (N : BoundedCounts n B)
    (raw : Molecule n → ℕ) (T : ℕ) (hN : boundedMass N ≤ T) (hraw : countMass raw ≤ T) :
    boundedMass (truncateCounts N raw) ≤ T := by
  unfold truncateCounts
  split_ifs
  · exact hraw
  · exact hN

theorem feed_raw_mass {n : ℕ} (N : Molecule n → ℕ) (f : Molecule n) :
    countMass (applyCountChannel N (fun _ => 0) (singleCount f)) = countMass N + molLength f := by
  change countMass (fun z => N z + singleCount f z) = _
  rw [countMass_add, countMass_single]

theorem bounded_food_mass_next_le {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (f : ↥(binaryFood n 2)) :
    boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inl f))) ≤
      boundedMass N + molLength f.val := by
  unfold boundedPhysicalCountModel
  dsimp only
  split_ifs
  · apply truncated_mass_upper
    · omega
    · change countMass (applyCountChannel (boundedCountsValue N) (fun _ => 0) (singleCount f.val)) ≤ _
      rw [feed_raw_mass]
      exact le_rfl
  · omega

theorem bounded_food_cubic_contribution_le {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (f : ↥(binaryFood n 2)) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inl (.inl f)) *
      (((boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inl f))) : ℝ) / V)^3 -
        ((boundedMass N : ℝ) / V)^3) ≤
    (D : ℝ)*V * ((((boundedMass N : ℝ) + molLength f.val) / V)^3 - ((boundedMass N : ℝ) / V)^3) := by
  rw [bounded_food_rate]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sub_le_sub_right
  have hmass : (boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inl f))) : ℝ) ≤
      (boundedMass N : ℝ) + molLength f.val := by
    exact_mod_cast bounded_food_mass_next_le c V D basal catalytic N f
  gcongr

theorem physical_outflow_rate {n : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (catalytic : Reaction n → Molecule n → NNReal) (N : Molecule n → ℕ) (z : Molecule n) :
    physicalChannelRate c V D basal catalytic N (.inl (.inr z)) = (D : ℝ)*N z := by
  simp [physicalChannelRate, physicalChannelInput, physicalChannelCoefficient, singleCount, apply_ite]
  field_simp [ne_of_gt hV]

theorem singleCount_enabled_iff {n : ℕ} (N : Molecule n → ℕ) (z : Molecule n) :
    (∀ w, singleCount z w ≤ N w) ↔ 1 ≤ N z := by
  constructor
  · intro h
    simpa [singleCount] using h z
  · intro h w
    by_cases hw : w=z
    · subst w
      simpa [singleCount] using h
    · simp [singleCount, hw]

theorem bounded_outflow_rate {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (catalytic : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B) (z : Molecule n) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inl (.inr z)) =
      (D : ℝ)*boundedCountsValue N z := by
  change (if ∀ w, singleCount z w ≤ boundedCountsValue N w then
    physicalChannelRate c V D basal catalytic (boundedCountsValue N) (.inl (.inr z)) else 0) = _
  split_ifs with h
  · exact physical_outflow_rate c V D hV basal catalytic _ z
  · have hn : ¬ 1 ≤ boundedCountsValue N z := fun hp => h ((singleCount_enabled_iff _ z).mpr hp)
    have hz : boundedCountsValue N z = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero]

theorem applyCountChannel_mass_accounting {n : ℕ} (N input output : Molecule n → ℕ)
    (henabled : ∀ z, input z ≤ N z) :
    countMass (applyCountChannel N input output) + countMass input = countMass N + countMass output := by
  unfold countMass applyCountChannel
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  have hh := congrArg (fun t => molLength z * t) (Nat.sub_add_cancel (henabled z))
  nlinarith

theorem bounded_outflow_mass_drop {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (z : Molecule n) (hz : 1 ≤ boundedCountsValue N z) :
    boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) +
      molLength z = boundedMass N := by
  have he : ∀ w, singleCount z w ≤ boundedCountsValue N w := (singleCount_enabled_iff _ z).mpr hz
  have hm := applyCountChannel_mass_accounting (boundedCountsValue N) (singleCount z) (fun _ => 0) he
  have hzero : countMass (fun _ : Molecule n => 0) = 0 := by simp [countMass]
  rw [countMass_single, hzero, Nat.add_zero] at hm
  change boundedMass (if ∀ w, singleCount z w ≤ boundedCountsValue N w then
    truncateCounts N (applyCountChannel (boundedCountsValue N) (singleCount z) (fun _ => 0)) else N) + _ = _
  rw [if_pos he]
  unfold boundedMass
  rw [truncateCounts_preserves N _ (by have hb := N.property; change countMass (boundedCountsValue N) ≤ B at hb; omega)]
  exact hm

theorem bounded_outflow_cubic_numerator_le {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (z : Molecule n) :
    (boundedPhysicalCountModel c V D basal catalytic).rate N (.inl (.inr z)) *
      ((boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) : ℝ)^3 -
        (boundedMass N : ℝ)^3) ≤
      -(D : ℝ) * (boundedCountsValue N z : ℝ) * (molLength z : ℝ) * (boundedMass N : ℝ)^2 := by
  rw [bounded_outflow_rate c V D hV basal catalytic]
  by_cases hz : boundedCountsValue N z = 0
  · simp only [hz, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  · have hpos : 1 ≤ boundedCountsValue N z := by omega
    have hm := bounded_outflow_mass_drop c V D basal catalytic N z hpos
    have hmR : (boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) : ℝ) +
        molLength z = (boundedMass N : ℝ) := by exact_mod_cast hm
    have hl : (molLength z : ℝ) ≤ boundedMass N := by
      exact_mod_cast (show molLength z ≤ boundedMass N by omega)
    have hc := cubic_removal_bound (boundedMass N : ℝ) (molLength z : ℝ) (Nat.cast_nonneg _) hl
    have heq : (boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) : ℝ) =
        (boundedMass N : ℝ) - molLength z := by linarith
    rw [heq]
    have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ (D : ℝ)*(boundedCountsValue N z : ℝ) by positivity)
    nlinarith only [hh]

theorem bounded_mass_real_sum {n B : ℕ} (N : BoundedCounts n B) :
    ∑ z, (boundedCountsValue N z : ℝ) * (molLength z : ℝ) = (boundedMass N : ℝ) := by
  unfold boundedMass countMass
  push_cast
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem bounded_outflow_cubic_sum_le {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    ∑ z, (boundedPhysicalCountModel c V D basal catalytic).rate N (.inl (.inr z)) *
      (((boundedMass ((boundedPhysicalCountModel c V D basal catalytic).next N (.inl (.inr z))) : ℝ) / V)^3 -
        ((boundedMass N : ℝ) / V)^3) ≤ -(D : ℝ) * ((boundedMass N : ℝ) / V)^3 := by
  have hn := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    bounded_outflow_cubic_numerator_le c V D hV basal catalytic N z)
  have hs : (∑ z, -(D : ℝ) * (boundedCountsValue N z : ℝ) * (molLength z : ℝ) * (boundedMass N : ℝ)^2) =
      -(D : ℝ) * (boundedMass N : ℝ)^3 := by
    calc
      _ = (-(D : ℝ) * (boundedMass N : ℝ)^2) *
          (∑ z, (boundedCountsValue N z : ℝ) * (molLength z : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [bounded_mass_real_sum]; ring
  rw [hs] at hn
  have hd := div_le_div_of_nonneg_right hn (show 0 ≤ (V : ℝ)^3 by positivity)
  simpa only [Finset.sum_div, div_pow, mul_div_assoc, sub_div] using hd

/-- The actual finite reactor generator is bounded by its food arrivals and
the negative cubic dilution term. Internal chemistry cancels exactly. -/
theorem bounded_cubic_generator_food_bound {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    (boundedPhysicalCountModel c V D basal catalytic).generator
      (fun X => ((boundedMass X : ℝ) / V)^3) N ≤
    (∑ f : ↥(binaryFood n 2), (D : ℝ)*V *
      ((((boundedMass N : ℝ) + molLength f.val) / V)^3 - ((boundedMass N : ℝ) / V)^3)) -
      (D : ℝ) * ((boundedMass N : ℝ) / V)^3 := by
  unfold FiniteJumpModel.generator
  rw [Fintype.sum_sum_type]
  rw [bounded_internal_cubic_sum_zero, add_zero, Fintype.sum_sum_type]
  have hf := Finset.sum_le_sum (fun f (_ : f ∈ Finset.univ) =>
    bounded_food_cubic_contribution_le c V D basal catalytic N f)
  have hd := bounded_outflow_cubic_sum_le c V D hV basal catalytic N
  linarith only [hf, hd]

def foodWordEquiv {n : ℕ} (hn : 2 ≤ n) : ↥(binaryFood n 2) ≃ Molecule 2 where
  toFun x := ⟨⟨x.val.1.val, by
    have hx := (Finset.mem_filter.mp x.property).2
    dsimp [molLength] at hx
    omega⟩, x.val.2⟩
  invFun y := ⟨⟨⟨y.1.val, by have hy := y.1.isLt; omega⟩, y.2⟩, by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp [molLength]
    have hy := y.1.isLt
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem food_length_sum {n : ℕ} (hn : 2 ≤ n) (g : ℕ → ℝ) :
    (∑ f : ↥(binaryFood n 2), g (molLength f.val)) = 2*g 1+4*g 2 := by
  calc
    _ = ∑ z : Molecule 2, g (molLength z) := by
      apply Fintype.sum_equiv (foodWordEquiv hn)
      intro x
      rfl
    _ = _ := by
      simp [Fintype.sum_sigma, Fin.sum_univ_succ, molLength, RAF.Polymer.Word]
      left
      ring

theorem bounded_cubic_generator_drift {n B : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) :
    (boundedPhysicalCountModel c V D basal catalytic).generator
      (fun X => ((boundedMass X : ℝ) / V)^3) N ≤
      (D : ℝ) * (19000 - ((boundedMass N : ℝ) / V)^3 / 2) := by
  have hVp : 0 < (V : ℝ) := by linarith
  have hb := bounded_cubic_generator_food_bound c V D hVp basal catalytic N
  rw [food_length_sum hn (fun l => (D : ℝ)*V * ((((boundedMass N : ℝ) + (l : ℝ)) / V)^3 - ((boundedMass N : ℝ) / V)^3))] at hb
  have he : 2 * ((D : ℝ)*V * ((((boundedMass N : ℝ)+1)/V)^3-((boundedMass N : ℝ)/V)^3)) +
      4 * ((D : ℝ)*V * ((((boundedMass N : ℝ)+2)/V)^3-((boundedMass N : ℝ)/V)^3)) -
      (D : ℝ)*((boundedMass N : ℝ)/V)^3 =
      (D : ℝ)*(30*((boundedMass N : ℝ)/V)^2+54*((boundedMass N : ℝ)/V)/V+34/(V : ℝ)^2-
        ((boundedMass N : ℝ)/V)^3) := by
    field_simp
    ring
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at hb
  rw [he] at hb
  exact hb.trans (physical_cubic_drift_bound _ _ _ (by positivity) hV D.coe_nonneg)

end
end RandomViability



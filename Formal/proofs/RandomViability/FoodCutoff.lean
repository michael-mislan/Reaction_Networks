import proofs.RandomViability.FoodReference
import proofs.RandomViability.BasalQuietBound

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

theorem food_count_mass_bound {n : ℕ} (hn : 2 ≤ n) (N : Molecule n → ℕ)
    (hN : foodCountSupported N) (u : ℕ) (hu : ∀ z ∈ binaryFood n 2, N z ≤ u) :
    countMass N ≤ 10*u := by
  have hs : (∑ z ∈ binaryFood n 2, molLength z) = 10 := by
    rw [Finset.sum_subtype (p := fun z => z ∈ binaryFood n 2) (binaryFood n 2) (fun _ => Iff.rfl)]
    have hh := food_length_sum hn (fun l => (l : ℝ))
    norm_num at hh
    exact_mod_cast hh
  have he : countMass N = ∑ z ∈ binaryFood n 2, molLength z*N z := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro z _ hz
    have hz0 : N z=0 := by
      by_contra h
      exact hz (hN z (by omega))
    simp only [hz0, mul_zero]
  rw [he]
  calc
    _ ≤ ∑ z ∈ binaryFood n 2, molLength z*u := Finset.sum_le_sum (fun z hz => Nat.mul_le_mul_left _ (hu z hz))
    _ = (∑ z ∈ binaryFood n 2, molLength z)*u := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [hs]

theorem bounded_feed_count_exact {n B : ℕ} (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (f : ↥(binaryFood n 2))
    (hmass : countMass (boundedCountsValue N)+molLength f.val ≤ B) :
    boundedCountsValue ((boundedPhysicalCountModel c V D basal cat).next N (.inl (.inl f))) =
      fun z => boundedCountsValue N z+singleCount f.val z := by
  have hraw : countMass (applyCountChannel (boundedCountsValue N) (fun _ => 0) (singleCount f.val)) ≤ B := by
    rw [feed_raw_mass]
    exact hmass
  change boundedCountsValue (if ∀ z, (0 : ℕ) ≤ boundedCountsValue N z then
    truncateCounts N (applyCountChannel (boundedCountsValue N) (fun _ => 0) (singleCount f.val)) else N) = _
  rw [if_pos (fun _ => Nat.zero_le _), truncateCounts_preserves N _ hraw]
  rfl

theorem bounded_corridor_feed_count_exact {n B : ℕ} (hn : 2 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V D : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : BoundedCounts n B) (hN : foodCountSupported (boundedCountsValue N))
    (u : ℕ) (hu : ∀ z ∈ binaryFood n 2, boundedCountsValue N z ≤ u) (hB : 10*u+2 ≤ B)
    (f : ↥(binaryFood n 2)) :
    boundedCountsValue ((boundedPhysicalCountModel c V D basal cat).next N (.inl (.inl f))) =
      fun z => boundedCountsValue N z+singleCount f.val z := by
  apply bounded_feed_count_exact
  have hm := food_count_mass_bound hn (boundedCountsValue N) hN u hu
  have hf : molLength f.val ≤ 2 := (Finset.mem_filter.mp f.property).2
  omega

theorem cushioned_basal_hazard {n B : ℕ} (c : SourceMoleculeFibreConfig n)
    (V D ε : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal) (N : BoundedCounts n B)
    (hcap : ∀ r, (basal r : ℝ) ≤ 4*ε) (hB : (B : ℝ) ≤ 12*V+2) :
    boundedBasalIntensity c V D basal cat N ≤ 624*ε*V+200*ε+16*ε/V := by
  have hmass : (B : ℝ) ≤ (12+2/(V : ℝ))*V := by
    have he : (12+2/(V : ℝ))*V=12*V+2 := by field_simp
    rw [he]
    exact hB
  have hh := bounded_basal_intensity_cutoff_bound c V D hV basal cat N (4*ε) (12+2/(V : ℝ))
    (by positivity) (by positivity) hcap hmass
  calc
    _ ≤ (4*(ε : ℝ))*V*((12+2/(V : ℝ))^2+(12+2/(V : ℝ))) := hh
    _ = _ := by field_simp; ring

end
end RandomViability

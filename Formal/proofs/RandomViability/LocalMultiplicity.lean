import proofs.RandomViability.LocalRectangleErrorLimit

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 70000

def localReactionSet (n K : ℕ) : Finset (Reaction n) :=
  Finset.univ.filter (fun r => reactionProductLength r ≤ K+2)

theorem local_count_le_one_iff {n K : ℕ} (c : SourceMoleculeFibreConfig n) :
    localRectangleCount (binaryFood n K) (localReactionSet n K) c ≤ 1 ↔ AtMostOneLocalIncidence K c := by
  simp only [localRectangleCount,Finset.sum_boole,Nat.cast_id,Finset.card_le_one]
  constructor
  · intro hh z r z' r' h h'
    have hm (z : Molecule n) (r : Reaction n) (h : LocalIncidence K c z r) :
        (z,r) ∈ ((binaryFood n K).product (localReactionSet n K)).filter (fun i => i.2 ∈ c i.1) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.1⟩⟩,h.2.2⟩
    have he := hh (z,r) (hm z r h) (z',r') (hm z' r' h')
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  · intro hh i hi j hj
    have hm (i : Molecule n × Reaction n)
        (hi : i ∈ ((binaryFood n K).product (localReactionSet n K)).filter (fun i => i.2 ∈ c i.1)) :
        LocalIncidence K c i.1 i.2 := by
      obtain ⟨hi,hc⟩ := Finset.mem_filter.mp hi
      obtain ⟨hz,hr⟩ := Finset.mem_product.mp hi
      exact ⟨(Finset.mem_filter.mp hz).2,(Finset.mem_filter.mp hr).2,hc⟩
    exact Prod.ext (hh i.1 i.2 j.1 j.2 (hm i hi) (hm j hj)).1
      (hh i.1 i.2 j.1 j.2 (hm i hi) (hm j hj)).2

theorem local_reaction_card_le (n K : ℕ) :
    (localReactionSet n K).card ≤ Fintype.card (Reaction (K+2)) := by
  have he : (localReactionSet n K).card = Fintype.card (ShortProductReaction n (K+2)) := by
    simp only [localReactionSet,ShortProductReaction,Fintype.card_subtype]
  rw [he]
  exact shortProductReaction_card_le n (K+2)

theorem two_local_mass_le_rectangle_error (a : ℝ) (n K : ℕ) (ha : 1 < a) (hn : 4 ≤ n) :
    eventMass a n (fun c => ¬AtMostOneLocalIncidence K c) ≤
      localRectangleError a n (binaryFood n K).card (localReactionSet n K).card := by
  have he : (fun c : SourceMoleculeFibreConfig n => ¬AtMostOneLocalIncidence K c) =
      (fun c => 2 ≤ localRectangleCount (binaryFood n K) (localReactionSet n K) c) := by
    funext c
    apply propext
    rw [← local_count_le_one_iff]
    omega
  rw [he]
  by_cases hT : (localReactionSet n K).card = 0
  · have hempty := Finset.card_eq_zero.mp hT
    simp [hempty,eventMass,localRectangleCount,localRectangleError]
  · exact local_rectangle_quadratic_bound a ha hn (binaryFood n K) (localReactionSet n K) (by omega)

theorem two_local_mass_scaled_tendsto_zero (K : ℕ) :
    Tendsto (fun n : ℕ => (sourceMoleculeCount n : ℝ)*
      eventMass (2-2/(n : ℝ)) n (fun c => ¬AtMostOneLocalIncidence K c)) atTop (𝓝 0) := by
  have he := bounded_rectangle_error_scaled_tendsto (Fintype.card (Molecule K))
    (Fintype.card (Reaction (K+2))) (fun n => (binaryFood n K).card)
    (fun n => (localReactionSet n K).card)
    (fun n => HordijkSteelThreshold.binaryFood_card_le_cutoff n K)
    (fun n => local_reaction_card_le n K)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards [sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n ha
    exact mul_nonneg (Nat.cast_nonneg _) (eventMass_nonneg _ n ha _)
  · filter_upwards [eventually_ge_atTop 4,
      sourceExactCriticalExponent_tendsto.eventually (Ioi_mem_nhds one_lt_two)] with n hn ha
    exact mul_le_mul_of_nonneg_left (two_local_mass_le_rectangle_error _ n K ha hn) (Nat.cast_nonneg _)

/-- H2 at the required vanishing single-incidence scale. -/
theorem two_local_incidence_mass_div_incidence_tendsto_zero (K : ℕ) :
    Tendsto (fun n : ℕ => eventMass (2-2/(n : ℝ)) n (fun c => ¬AtMostOneLocalIncidence K c)/
      (windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/(sourceReactionCount n : ℝ)))
      atTop (𝓝 0) := by
  have hh := (two_local_mass_scaled_tendsto_zero K).div sourceExactCriticalFirstMoment_scaled_tendsto
    (ne_of_gt (criticalLambda_pos (-2)))
  simp only [zero_div] at hh
  apply hh.congr'
  filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn
  have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp only [Pi.div_apply]
  field_simp

end
end RandomViability

import proofs.RandomViability.PhysicalPairEnvelope

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 150000

def physicalCoordinateDrift {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) : ℝ :=
  ∑ ch, unboundedPhysicalRate c V 1 basal cat N ch*coordinateConcentrationJump V q N ch

theorem rate_weighted_coordinate_change {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) (ch : PhysicalCountChannel n) :
    unboundedPhysicalRate c V 1 basal cat N ch*coordinateConcentrationJump V q N ch =
      unboundedPhysicalRate c V 1 basal cat N ch*
        ((physicalChannelOutput ch q : ℝ)-(physicalChannelInput ch q : ℝ))/V := by
  by_cases he : ∀ z,physicalChannelInput ch z ≤ N z
  · simp only [coordinateConcentrationJump,unboundedPhysicalNext,if_pos he]
    rw [coordinate_raw_change N _ _ he]
    ring
  · simp [unboundedPhysicalRate,he]

def reactionCoordinateChange {n : ℕ} (r : Reaction n) (q : Molecule n) : ℝ :=
  (singleCount (reactionProduct r) q : ℝ)-
    ((singleCount (reactionLeft r) q : ℝ)+singleCount (reactionRight r) q)

theorem physical_coordinate_drift_decomposition {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (q : Molecule n) :
    physicalCoordinateDrift c V basal cat N q =
      (if molLength q ≤ 2 then 1 else 0)-(N q : ℝ)/V +
      ∑ r, (physicalPairFlux c V basal cat N r true-
        physicalPairFlux c V basal cat N r false)*reactionCoordinateChange r q := by
  let R := unboundedPhysicalRate c V 1 basal cat N
  have hf : (∑ f : ↥(binaryFood n 2), R (.inl (.inl f))*
      ((physicalChannelOutput (.inl (.inl f)) q : ℝ)-physicalChannelInput (.inl (.inl f)) q)/V) =
      if molLength q ≤ 2 then 1 else 0 := by
    simp only [R,unbounded_feed_rate,NNReal.coe_one,one_mul,physicalChannelOutput,
      physicalChannelInput,Nat.cast_zero,sub_zero]
    simp only [mul_div_cancel_left₀ _ (ne_of_gt hV)]
    by_cases hq : molLength q ≤ 2
    · let f : ↥(binaryFood n 2) := ⟨q,by simp [binaryFood,hq]⟩
      have he : ∀ b : ↥(binaryFood n 2), q = b.val ↔ b = f := by
        intro b
        exact ⟨fun h => Subtype.ext h.symm,fun h => congrArg Subtype.val h.symm⟩
      simp [singleCount,he,hq]
    · have he : ∀ b : ↥(binaryFood n 2), q ≠ b.val := by
        intro b h
        have hb : molLength b.val ≤ 2 := (Finset.mem_filter.mp b.property).2
        exact hq (h ▸ hb)
      simp [singleCount,he,hq]
  have ho : (∑ z : Molecule n,R (.inl (.inr z))*
      ((physicalChannelOutput (.inl (.inr z)) q : ℝ)-physicalChannelInput (.inl (.inr z)) q)/V) =
      -(N q : ℝ)/V := by
    have hr : ∀ z,R (.inl (.inr z)) = (N z : ℝ) := by
      intro z
      have hh := bounded_outflow_rate c V 1 hV basal cat (countsAtOwnMass N) z
      simpa only [NNReal.coe_one,one_mul] using hh
    simp only [hr,physicalChannelOutput,physicalChannelInput,Nat.cast_zero,zero_sub,
      mul_neg,← Finset.sum_div]
    simp [singleCount]
  have hb : ∀ r, (∑ d : Bool,R (.inr (.inl (r,d)))*
      ((physicalChannelOutput (.inr (.inl (r,d))) q : ℝ)-physicalChannelInput (.inr (.inl (r,d))) q)/V) =
      (R (.inr (.inl (r,true)))-R (.inr (.inl (r,false))))/V*reactionCoordinateChange r q := by
    intro r
    simp only [Fintype.sum_bool,physicalChannelOutput,physicalChannelInput,
      Bool.false_eq_true,if_false,if_true,Nat.cast_add,reactionCoordinateChange]
    ring
  have hc : ∀ r z, (∑ d : Bool,R (.inr (.inr (r,z,d)))*
      ((physicalChannelOutput (.inr (.inr (r,z,d))) q : ℝ)-physicalChannelInput (.inr (.inr (r,z,d))) q)/V) =
      (R (.inr (.inr (r,z,true)))-R (.inr (.inr (r,z,false))))/V*reactionCoordinateChange r q := by
    intro r z
    simp only [Fintype.sum_bool,physicalChannelOutput,physicalChannelInput,
      Bool.false_eq_true,if_false,if_true,Nat.cast_add,reactionCoordinateChange]
    ring
  dsimp only [R] at hf ho hb hc
  unfold physicalCoordinateDrift
  simp only [rate_weighted_coordinate_change,Fintype.sum_sum_type,Fintype.sum_prod_type]
  change (_+_)+(_+_) = _
  rw [hf,ho]
  simp only [hb,hc]
  rw [← Finset.sum_add_distrib]
  simp only [neg_div,← sub_eq_add_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  simp only [← Finset.sum_mul,← Finset.sum_div,Finset.sum_sub_distrib,physicalPairFlux]
  ring

/-- Literal internal drift is bounded below by the mass-action loss envelope.
No mass-action approximation is asserted for the actual gains. -/
theorem physical_coordinate_drift_lower {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (C : ℝ)
    (hflux : ∀ r d,physicalPairFlux c V basal cat N r d ≤ C*
      (if d then ((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)
       else (N (reactionProduct r) : ℝ)/V)) (q : Molecule n) :
    (if molLength q ≤ 2 then 1 else 0)-(N q : ℝ)/V-
      collectiveLoss (fun _ => C) (fun z => (N z : ℝ)/V) q ≤
      physicalCoordinateDrift c V basal cat N q := by
  rw [physical_coordinate_drift_decomposition c V hV basal cat N q]
  suffices hh : -collectiveLoss (fun _ => C) (fun z => (N z : ℝ)/V) q ≤
      ∑ r,(physicalPairFlux c V basal cat N r true-
        physicalPairFlux c V basal cat N r false)*reactionCoordinateChange r q by linarith
  unfold collectiveLoss
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro r _
  have hF := hflux r true
  have hB := hflux r false
  have hF0 := physical_pair_flux_nonneg c V basal cat N r true
  have hB0 := physical_pair_flux_nonneg c V basal cat N r false
  simp only [if_true,Bool.false_eq_true,if_false] at hF hB
  unfold reactionCoordinateChange singleCount
  simp only [eq_comm (a := q)]
  split_ifs <;> norm_num <;> nlinarith only [hF,hB,hF0,hB0]

end
end RandomViability

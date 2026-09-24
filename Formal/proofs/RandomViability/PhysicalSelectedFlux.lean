import proofs.RandomViability.PhysicalPairEnvelope
import proofs.RandomViability.ProductiveRates

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

theorem basal_distinct_monomial_lower {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (huw : reactionLeft r ≠ reactionRight r) :
    (basal r : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r))/V ≤
      unboundedPhysicalRate c V 1 basal cat N (.inr (.inl (r,true))) := by
  by_cases hu : 1 ≤ N (reactionLeft r)
  · by_cases hw : 1 ≤ N (reactionRight r)
    · exact le_of_eq (bounded_basal_ligation_rate_distinct c V 1 hV basal cat
        (countsAtOwnMass N) r huw hu hw).symm
    · have hz : N (reactionRight r) = 0 := by omega
      simpa only [hz,Nat.cast_zero,mul_zero,zero_div] using
        unboundedPhysicalRate_nonneg c V 1 basal cat N (.inr (.inl (r,true)))
  · have hz : N (reactionLeft r) = 0 := by omega
    simpa only [hz,Nat.cast_zero,zero_mul,mul_zero,zero_div] using
      unboundedPhysicalRate_nonneg c V 1 basal cat N (.inr (.inl (r,true)))

theorem catalytic_distinct_monomial_lower {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (z : Molecule n)
    (huw : reactionLeft r ≠ reactionRight r) (huz : reactionLeft r ≠ z)
    (hwz : reactionRight r ≠ z) (hsel : r ∈ c z) :
    (cat r z : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r)*N z)/(V : ℝ)^2 ≤
      unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,true))) := by
  by_cases hu : 1 ≤ N (reactionLeft r)
  · by_cases hw : 1 ≤ N (reactionRight r)
    · by_cases hz : 1 ≤ N z
      · exact le_of_eq (unbounded_catalytic_ligation_rate_distinct c V 1 hV basal cat N r z
          huw huz hwz hu hw hz hsel).symm
      · have hzero : N z = 0 := by omega
        simpa only [hzero,Nat.cast_zero,mul_zero,zero_div] using
          unboundedPhysicalRate_nonneg c V 1 basal cat N (.inr (.inr (r,z,true)))
    · have hzero : N (reactionRight r) = 0 := by omega
      simpa only [hzero,Nat.cast_zero,mul_zero,zero_mul,zero_div] using
        unboundedPhysicalRate_nonneg c V 1 basal cat N (.inr (.inr (r,z,true)))
  · have hzero : N (reactionLeft r) = 0 := by omega
    simpa only [hzero,Nat.cast_zero,zero_mul,mul_zero,zero_div] using
      unboundedPhysicalRate_nonneg c V 1 basal cat N (.inr (.inr (r,z,true)))

/-- Exact distinct-input regeneration survives down to zero copies. -/
theorem physical_selected_flux_lower {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (huw : reactionLeft r ≠ reactionRight r)
    (huz : reactionLeft r ≠ reactionProduct r) (hwz : reactionRight r ≠ reactionProduct r)
    (hsel : r ∈ c (reactionProduct r)) (eps : ℝ)
    (hb : eps ≤ (basal r : ℝ)) (hc : 4 ≤ (cat r (reactionProduct r) : ℝ)) :
    (eps+4*((N (reactionProduct r) : ℝ)/V))*
      ((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V) ≤
      physicalPairFlux c V basal cat N r true := by
  have hbas := basal_distinct_monomial_lower c V hV basal cat N r huw
  have hcat := catalytic_distinct_monomial_lower c V hV basal cat N r (reactionProduct r)
    huw huz hwz hsel
  have hs := Finset.single_le_sum
    (f := fun z => unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,true))))
    (fun z _ => unboundedPhysicalRate_nonneg c V 1 basal cat N _) (Finset.mem_univ (reactionProduct r))
  have hb' := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (N (reactionLeft r) : ℝ)*N (reactionRight r) by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (N (reactionLeft r) : ℝ)*N (reactionRight r)*N (reactionProduct r) by positivity)
  have hh := div_le_div_of_nonneg_right
    (add_le_add ((div_le_div_of_nonneg_right hb' hV.le).trans hbas)
      ((div_le_div_of_nonneg_right hc' (sq_nonneg _)).trans (hcat.trans hs))) hV.le
  unfold physicalPairFlux
  convert hh using 1
  ring

end
end RandomViability

import proofs.RandomViability.PhysicalCoordinateVariance
import proofs.RandomViability.CollectiveDrift

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

/-- Literal basal plus all selected catalytic intensities, per unit volume. -/
def physicalPairFlux {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (d : Bool) : ℝ :=
  (unboundedPhysicalRate c V 1 basal cat N (.inr (.inl (r,d))) +
    ∑ z, unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d))))/V

theorem physical_pair_flux_nonneg {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (d : Bool) :
    0 ≤ physicalPairFlux c V basal cat N r d := by
  apply div_nonneg _ V.coe_nonneg
  exact add_nonneg (unboundedPhysicalRate_nonneg c V 1 basal cat N _)
    (Finset.sum_nonneg (fun z _ => unboundedPhysicalRate_nonneg c V 1 basal cat N _))

theorem physical_pair_flux_envelope {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n) (d : Bool) :
    physicalPairFlux c V basal cat N r d ≤
      collectivePairSpeed c (fun r => basal r) (fun r z => cat r z)
        (fun z => (N z : ℝ)/V) r *
      (if d then ((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)
       else (N (reactionProduct r) : ℝ)/V) := by
  let x : Molecule n → ℝ := fun z => (N z : ℝ)/V
  let m : ℝ := if d then x (reactionLeft r)*x (reactionRight r) else x (reactionProduct r)
  have hb : unboundedPhysicalRate c V 1 basal cat N (.inr (.inl (r,d)))/V ≤
      (basal r : ℝ)*m := by
    cases d with
    | false =>
      have hh := bounded_basal_cleavage_rate_le c V 1 hV basal cat (countsAtOwnMass N) r
      change unboundedPhysicalRate c V 1 basal cat N _ ≤ (basal r : ℝ)*N (reactionProduct r) at hh
      exact (div_le_div_of_nonneg_right hh hV.le).trans_eq (by dsimp [m,x]; ring)
    | true =>
      have hh := bounded_basal_ligation_rate_le c V 1 hV basal cat (countsAtOwnMass N) r
      change unboundedPhysicalRate c V 1 basal cat N _ ≤
        (basal r : ℝ)*((N (reactionLeft r) : ℝ)*N (reactionRight r))/V at hh
      exact (div_le_div_of_nonneg_right hh hV.le).trans_eq (by dsimp [m,x]; ring)
  have hc : ∀ z, unboundedPhysicalRate c V 1 basal cat N (.inr (.inr (r,z,d)))/V ≤
      (if r ∈ c z then (cat r z : ℝ)*x z else 0)*m := by
    intro z
    by_cases hs : r ∈ c z
    · rw [if_pos hs]
      cases d with
      | false =>
        have hh := unbounded_catalytic_cleavage_rate_le c V 1 hV basal cat N r z
          (cat r z) (cat r z).coe_nonneg le_rfl
        exact (div_le_div_of_nonneg_right hh hV.le).trans_eq (by dsimp [m,x]; ring)
      | true =>
        have hh := unbounded_catalytic_ligation_rate_le c V 1 hV basal cat N r z
          (cat r z) (cat r z).coe_nonneg le_rfl
        exact (div_le_div_of_nonneg_right hh hV.le).trans_eq (by dsimp [m,x]; ring)
    · simp [unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,hs]
  change _ ≤ collectivePairSpeed c (fun r => basal r) (fun r z => cat r z) x r*m
  unfold physicalPairFlux
  rw [add_div,Finset.sum_div]
  calc
    _ ≤ (basal r : ℝ)*m + ∑ z, (if r ∈ c z then (cat r z : ℝ)*x z else 0)*m :=
      add_le_add hb (Finset.sum_le_sum (fun z _ => hc z))
    _ = _ := by rw [← Finset.sum_mul,← add_mul]; rfl

/-- Food-row emptiness removes catalog-size dependence from both directions. -/
theorem physical_pair_flux_nonfood_bound {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (eps : ℝ)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*eps) (hc : ∀ r z,(cat r z : ℝ) ≤ 16)
    (hfood : ∀ z,molLength z ≤ 2 → c z = ∅) (r : Reaction n) (d : Bool) :
    physicalPairFlux c V basal cat N r d ≤
      (4*eps+(16/3)*nonfoodMass (fun z => (N z : ℝ)/V))*
      (if d then ((N (reactionLeft r) : ℝ)/V)*((N (reactionRight r) : ℝ)/V)
       else (N (reactionProduct r) : ℝ)/V) := by
  apply (physical_pair_flux_envelope c V hV basal cat N r d).trans
  apply mul_le_mul_of_nonneg_right
    (collective_pair_speed_bound c (fun r => basal r) (fun r z => cat r z)
      (fun z => (N z : ℝ)/V) (fun z => by positivity) eps hb hc hfood r)
  cases d <;> simp only [Bool.false_eq_true,if_false,if_true] <;> positivity

end
end RandomViability

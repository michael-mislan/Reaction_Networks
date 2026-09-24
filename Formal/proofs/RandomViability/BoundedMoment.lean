import proofs.RandomViability.BoundedMassDrift
import proofs.RandomViability.KernelReward

namespace RandomViability
open Classical RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section

theorem bounded_cubic_uniformize_step {n B : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (q : ℝ) (hq : 0 < q)
    (hbound : ∀ X, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q)
    (N : BoundedCounts n B) :
    ((boundedPhysicalCountModel c V D basal catalytic).uniformize q hq hbound).step
      (fun X => ((boundedMass X : ℝ) / V)^3) N ≤
      (1-(D : ℝ)/(2*q))*((boundedMass N : ℝ)/V)^3 +
        (1-(1-(D : ℝ)/(2*q)))*38000 := by
  rw [FiniteJumpModel.uniformize_step]
  have hd := div_le_div_of_nonneg_right
    (bounded_cubic_generator_drift hn c V D hV basal catalytic N) hq.le
  calc
    _ ≤ ((boundedMass N : ℝ)/V)^3 +
        (D : ℝ)*(19000-((boundedMass N : ℝ)/V)^3/2)/q := add_le_add (le_refl _) hd
    _ = _ := by ring

/-- The moment conclusion is derived for the actual finite reactor kernel;
only the initial state, volume and uniformization rate are bounded. -/
theorem bounded_poissonized_cubic_moment {n B : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V D : NNReal) (hV : 1 ≤ (V : ℝ))
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal)
    (q : ℝ) (hq : 0 < q) (hqD : (D : ℝ) ≤ 2*q)
    (hbound : ∀ X, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q)
    (N : BoundedCounts n B) (hinit : ((boundedMass N : ℝ)/V)^3 ≤ 38000)
    (t : NNReal) :
    ((boundedPhysicalCountModel c V D basal catalytic).uniformize q hq hbound).poissonized
      t (fun X => ((boundedMass X : ℝ) / V)^3) N ≤ 38000 := by
  apply poissonized_moment_bound _ _ (1-(D : ℝ)/(2*q)) 38000
  · exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hqD)
  · intro X
    positivity
  · intro X
    exact bounded_cubic_uniformize_step hn c V D hV basal catalytic q hq hbound X
  · exact hinit

theorem bounded_uniformization_rate_exists {n B : ℕ}
    (c : SourceMoleculeFibreConfig n) (V D : NNReal)
    (basal : Reaction n → NNReal) (catalytic : Reaction n → Molecule n → NNReal) :
    ∃ q : ℝ, 0 < q ∧ (D : ℝ) ≤ 2*q ∧
      ∀ X : BoundedCounts n B, (boundedPhysicalCountModel c V D basal catalytic).total X ≤ q := by
  let M : FiniteJumpModel (BoundedCounts n B) (PhysicalCountChannel n) := boundedPhysicalCountModel c V D basal catalytic
  have ht : ∀ X : BoundedCounts n B, 0 ≤ M.total X := by
    intro X
    exact Finset.sum_nonneg (fun ch _ => M.nonneg X ch)
  have hs : 0 ≤ ∑ X : BoundedCounts n B, M.total X := Finset.sum_nonneg (fun X _ => ht X)
  refine ⟨1+(D : ℝ)+∑ X : BoundedCounts n B, M.total X, ?_, ?_, ?_⟩
  · linarith [D.coe_nonneg]
  · linarith [D.coe_nonneg]
  · intro X
    have hx := Finset.single_le_sum (fun Y (_ : Y ∈ Finset.univ) => ht Y) (Finset.mem_univ X)
    change M.total X ≤ _
    linarith [D.coe_nonneg]

end
end RandomViability


import proofs.RandomViability.CoordinateMaximal

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def coordinateNoiseTheta (V δ T : ℝ) : ℝ := δ*V/(2*(96000*T+2*δ))

theorem coordinate_noise_scale (V δ T : ℝ) (hV : 0 < V) (hδ : 0 < δ) (hT : 0 ≤ T) :
    0 ≤ coordinateNoiseTheta V δ T ∧
    |coordinateNoiseTheta V δ T| *(2/V) ≤ 1 ∧
    -coordinateNoiseTheta V δ T*δ+(coordinateNoiseTheta V δ T)^2*(96000/V)*T ≤
      -(δ^2*V/(4*(96000*T+2*δ))) := by
  let A := 96000*T+2*δ
  let θ := coordinateNoiseTheta V δ T
  have hA : 0 < A := by dsimp [A]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ,coordinateNoiseTheta]; positivity
  have ht : |θ| *(2/V) ≤ 1 := by
    rw [abs_of_nonneg hθ]
    have he : θ*(2/V) = δ/A := by
      dsimp [θ,coordinateNoiseTheta,A]
      field_simp
    rw [he]
    apply (div_le_one hA).mpr
    dsimp [A]
    linarith
  have hratio : 96000*T/A ≤ 1 := (div_le_one hA).mpr (by dsimp [A]; linarith)
  have hcost : θ^2*(96000/V)*T ≤ θ*δ/2 := by
    calc
      _ = (θ*δ/2)*(96000*T/A) := by
        dsimp [θ,coordinateNoiseTheta,A]
        field_simp
      _ ≤ (θ*δ/2)*1 := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := mul_one _
  refine ⟨hθ,ht,?_⟩
  calc
    _ ≤ -θ*δ/2 := by linarith
    _ = _ := by dsimp [θ,coordinateNoiseTheta]; field_simp; ring

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- Uniform two-sided coordinate compensation bound; no union cost in jump count. -/
theorem physical_coordinate_two_sided_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (δ T : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | ∃ K,δ ≤ |censoredCoordinatePrefix c V basal cat q T z K|} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(96000*T+2*δ))))) := by
  let μ := physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
  let θ := coordinateNoiseTheta V δ T
  let E := fun t : ℝ => ⋃ K,{z | coordinateTiltCrossingBy c V basal cat q t (θ*δ) T K z}
  let B := ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(96000*T+2*δ)))))
  have hs := coordinate_noise_scale V δ T hV hδ hT
  have hp : μ (E θ) ≤ B :=
    (physical_coordinate_any_index_tail hn c V hV basal cat N hbasal hcat q θ (θ*δ) T
      hs.2.1 hT).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        simpa only [neg_mul] using hs.2.2)))
  have hm : μ (E (-θ)) ≤ B :=
    (physical_coordinate_any_index_tail hn c V hV basal cat N hbasal hcat q (-θ) (θ*δ) T
      (by simpa only [abs_neg] using hs.2.1) hT).trans
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
          simpa only [neg_sq,neg_mul] using hs.2.2)))
  have hsub : {z | ∃ K,δ ≤ |censoredCoordinatePrefix c V basal cat q T z K|} ⊆ E θ ∪ E (-θ) := by
    intro z hz
    obtain ⟨K,hK⟩ := hz
    rcases le_abs.mp hK with hp|hm
    · apply Or.inl
      apply Set.mem_iUnion.mpr
      exact ⟨K,K,le_rfl,mul_le_mul_of_nonneg_left hp hs.1⟩
    · apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨K,K,le_rfl,?_⟩
      have hh := mul_le_mul_of_nonneg_left hm hs.1
      simpa only [mul_neg,neg_mul] using hh
  calc
    _ ≤ μ (E θ ∪ E (-θ)) := measure_mono hsub
    _ ≤ μ (E θ)+μ (E (-θ)) := measure_union_le _ _
    _ ≤ B+B := add_le_add hp hm
    _ = _ := (two_mul B).symm

end
end RandomViability

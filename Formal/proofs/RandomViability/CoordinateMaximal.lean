import proofs.RandomViability.CoordinateCompensation

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def coordinateTiltCrossingBy {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (q : Molecule n) (θ η T : ℝ) (K : ℕ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∃ j,j ≤ K ∧ η ≤ θ*censoredCoordinatePrefix c V basal cat q T z j

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

/-- A single signed estimate handles upper and lower coordinate fluctuations. -/
theorem physical_coordinate_crossing_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (θ η T : ℝ) (hθ : |θ| *(2/V) ≤ 1) (hT : 0 ≤ T) (K : ℕ) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      {z | coordinateTiltCrossingBy c V basal cat q θ η T K z} ≤
      ENNReal.ofReal (Real.exp (-η+θ^2*(96000/V)*T)) := by
  let μ := physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
  let κ := jumpHistoryKernel unboundedPhysicalNext (unboundedPhysicalRate c V 1 basal cat)
    (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  let m := coordinateCensoredMultiplier c V basal cat q θ T
  let L := η-θ^2*(96000/V)*T
  let a := ENNReal.ofReal (Real.exp L)
  let B := ENNReal.ofReal (Real.exp (-L))
  let W : Set (ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) :=
    {z | ∀ i,0 ≤ (z (i+1)).2.2}
  have hw : ∀ᵐ z ∂μ,z ∈ W := jumpTrajectory_wait_nonneg N unboundedPhysicalNext
    (unboundedPhysicalRate c V 1 basal cat) (unboundedPhysicalRate_nonneg c V 1 basal cat)
    (unbounded_total_pos hn c V 1 hV (by norm_num) basal cat)
  have hc := predictable_product_crossing_bound μ κ
    (fun k => physicalTrajectoryLaw_transition hn c V 1 hV (by norm_num) basal cat N k)
    m (coordinateCensoredMultiplier_measurable c V basal cat q θ T)
    (physical_censored_coordinate_mean hn c V hV basal cat hbasal hcat q θ T hθ) a K
  have hsub : W ∩ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z} ⊆
      {z | ∃ j,j ≤ K ∧ a ≤ trajectoryProduct m j z} := by
    intro z hz
    obtain ⟨j,hj,hA⟩ := hz.2
    refine ⟨j,hj,?_⟩
    dsimp only [m,a]
    rw [coordinate_product_exp]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht := censored_nonfood_time_bound V T hT (massExitStop V) z hz.1 j
    exact sub_le_sub hA (mul_le_mul_of_nonneg_left ht (by positivity))
  have heq : μ (W ∩ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z}) =
      μ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z} :=
    Measure.measure_inter_eq_of_ae hw
  have ht : a*μ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z} ≤ 1 := by
    rw [← heq]
    exact (mul_le_mul_right (measure_mono hsub) a).trans hc
  have hinv : B*a = 1 := by
    dsimp [B,a]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,neg_add_cancel,
      Real.exp_zero,ENNReal.ofReal_one]
  have hb : μ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z} ≤ B := by
    calc
      _ = B*(a*μ {z | coordinateTiltCrossingBy c V basal cat q θ η T K z}) := by
        rw [← mul_assoc,hinv,one_mul]
      _ ≤ B*1 := mul_le_mul_right ht B
      _ = _ := mul_one _
  have he : -L = -η+θ^2*(96000/V)*T := by dsimp [L]; ring
  simpa only [B,he] using hb

theorem physical_coordinate_any_index_tail (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r z,(cat r z : ℝ) ≤ 16)
    (q : Molecule n) (θ η T : ℝ) (hθ : |θ| *(2/V) ≤ 1) (hT : 0 ≤ T) :
    physicalTrajectoryLaw hn c V 1 hV (by norm_num) basal cat N
      (⋃ K,{z | coordinateTiltCrossingBy c V basal cat q θ η T K z}) ≤
      ENNReal.ofReal (Real.exp (-η+θ^2*(96000/V)*T)) := by
  have hm : Monotone (fun K => {z | coordinateTiltCrossingBy c V basal cat q θ η T K z}) := by
    intro K J hK z hz
    obtain ⟨j,hj,hA⟩ := hz
    exact ⟨j,hj.trans hK,hA⟩
  rw [hm.measure_iUnion]
  exact iSup_le (fun K => physical_coordinate_crossing_tail hn c V hV basal cat N
    hbasal hcat q θ η T hθ hT K)

end
end RandomViability

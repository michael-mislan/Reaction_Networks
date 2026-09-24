import proofs.HordijkSteelThreshold.FamilyOpenProbability
import Mathlib.Probability.Moments.Variance

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer RAF.Concrete

/-- Real-valued indicator that a target reaction family has at least one
supporting catalyst in the fixed prospective pool. -/
noncomputable def catalystPoolFamilyIndicator {n : Nat} (C : Finset (Molecule n))
    (R : Finset (Reaction n)) (ω : AmbientCoord n → Prop) : ℝ :=
  by
    classical
    exact if catalystPoolFamilyOpen ω C R then 1 else 0

theorem integral_catalystPoolFamilyIndicator_eq_measureReal {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    ∫ ω, catalystPoolFamilyIndicator C R ω ∂ambientPiMeasure n lambda =
      (ambientPiMeasure n lambda).real
        {ω | catalystPoolFamilyOpen ω C R} := by
  rw [show catalystPoolFamilyIndicator C R =
      {ω | catalystPoolFamilyOpen ω C R}.indicator (fun _ => (1 : ℝ)) by
        funext ω
        by_cases h : catalystPoolFamilyOpen ω C R <;>
          simp [catalystPoolFamilyIndicator, Set.indicator, h]]
  apply integral_indicator_one
  rw [show {ω | catalystPoolFamilyOpen ω C R} =
      (fun ω => catalystPoolFamilyOpen ω C R) ⁻¹' {True} by
        ext ω
        simp]
  exact (measurable_of_finite _) (measurableSet_singleton True)

theorem catalystPoolFamilyIndicator_memLp {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    MemLp (catalystPoolFamilyIndicator C R) 2 (ambientPiMeasure n lambda) := by
  classical
  apply memLp_of_bounded (a := (0 : ℝ)) (b := 1)
  · exact Filter.Eventually.of_forall fun ω => by
      by_cases h : catalystPoolFamilyOpen ω C R <;>
        simp [Set.mem_Icc, catalystPoolFamilyIndicator, h]
  · exact (measurable_of_finite _).aestronglyMeasurable

/-- The mean number of supported target families is exactly the sum of their
individual open probabilities.  No independence assumption is needed for
this identity. -/
theorem integral_sum_catalystPoolFamilyIndicator_eq {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*} (s : Finset ι)
    (R : ι → Finset (Reaction n)) :
    ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
        ∂ambientPiMeasure n lambda =
      ∑ i ∈ s, (ambientPiMeasure n lambda).real
        {ω | catalystPoolFamilyOpen ω C (R i)} := by
  classical
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_catalystPoolFamilyIndicator_eq_measureReal lambda C (R i)
  · intro i hi
    exact (catalystPoolFamilyIndicator_memLp lambda C (R i)).integrable one_le_two

/-- Real-valued cardinality form of the exact target-family open law. -/
theorem measureReal_catalystPoolFamilyOpen_card {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    (ambientPiMeasure n lambda).real {ω | catalystPoolFamilyOpen ω C R} =
      1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
        (C.card * R.card) := by
  rw [Measure.real_def, measure_catalystPoolFamilyOpen_card,
    ENNReal.toReal_sub_of_le]
  · simp
  · apply pow_le_one₀
    · simp
    · exact_mod_cast (σ (catalysisP n lambda)).2.2
  · simp

/-- A lower bound on the number of available reactions yields a uniform real
lower bound on the target-family open probability. -/
theorem one_sub_pow_le_measureReal_catalystPoolFamilyOpen {n d : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) (R : Finset (Reaction n))
    (hcard : d ≤ R.card) :
    1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * d) ≤
      (ambientPiMeasure n lambda).real
        {ω | catalystPoolFamilyOpen ω C R} := by
  rw [measureReal_catalystPoolFamilyOpen_card]
  apply sub_le_sub_left
  apply pow_le_pow_of_le_one
  · simpa using (catalysisP n lambda).2.2
  · exact_mod_cast (σ (catalysisP n lambda)).2.2
  · exact Nat.mul_le_mul_left C.card hcard

/-- A uniform lower bound on every target-family open probability gives the
corresponding linear lower bound on the expected supported-family count. -/
theorem card_mul_le_integral_sum_catalystPoolFamilyIndicator_of_le {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*} (s : Finset ι)
    (R : ι → Finset (Reaction n)) {p : ℝ}
    (hprob : ∀ i ∈ s, p ≤ (ambientPiMeasure n lambda).real
      {ω | catalystPoolFamilyOpen ω C (R i)}) :
    (s.card : ℝ) * p ≤
      ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
        ∂ambientPiMeasure n lambda := by
  rw [integral_sum_catalystPoolFamilyIndicator_eq]
  calc
    (s.card : ℝ) * p = ∑ _i ∈ s, p := by simp
    _ ≤ ∑ i ∈ s, (ambientPiMeasure n lambda).real
        {ω | catalystPoolFamilyOpen ω C (R i)} := by
      exact Finset.sum_le_sum fun i hi => hprob i hi

/-- Explicit fixed-state mean bound obtained from a uniform lower bound on
the number of viable reactions in every target family. -/
theorem card_mul_one_sub_pow_le_integral_sum_catalystPoolFamilyIndicator
    {n d : Nat} (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*}
    (s : Finset ι) (R : ι → Finset (Reaction n))
    (hcard : ∀ i ∈ s, d ≤ (R i).card) :
    (s.card : ℝ) *
        (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * d)) ≤
      ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
        ∂ambientPiMeasure n lambda := by
  apply card_mul_le_integral_sum_catalystPoolFamilyIndicator_of_le
  intro i hi
  exact one_sub_pow_le_measureReal_catalystPoolFamilyOpen
    lambda C (R i) (hcard i hi)

/-- Pairwise independence gives a sharp enough target-count concentration
input: the variance of the number of supported target families is at most one
quarter of the number of targets. -/
theorem variance_sum_catalystPoolFamilyIndicator_le {n : Nat} (lambda : ℝ)
    (C : Finset (Molecule n)) {ι : Type*} (s : Finset ι)
    (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j)) :
    variance (∑ i ∈ s, catalystPoolFamilyIndicator C (R i))
        (ambientPiMeasure n lambda) ≤ (s.card : ℝ) / 4 := by
  classical
  let X : ι → (AmbientCoord n → Prop) → ℝ :=
    fun i => catalystPoolFamilyIndicator C (R i)
  have hmem : ∀ i ∈ s, MemLp (X i) 2 (ambientPiMeasure n lambda) := by
    intro i _
    exact catalystPoolFamilyIndicator_memLp lambda C (R i)
  have hind : Set.Pairwise (↑s : Set ι) fun i j =>
      IndepFun (X i) (X j) (ambientPiMeasure n lambda) := by
    intro i _hi j _hj hij
    have hopen := pairwise_catalystPoolFamilyOpen_indep lambda C R hR hij
    let ind : Prop → ℝ := fun p => if p then 1 else 0
    have hcomp := hopen.comp (measurable_of_finite ind) (measurable_of_finite ind)
    change (fun ω => if catalystPoolFamilyOpen ω C (R i) then (1 : ℝ) else 0) ⟂ᵢ[
        ambientPiMeasure n lambda]
      (fun ω => if catalystPoolFamilyOpen ω C (R j) then (1 : ℝ) else 0)
    simpa [ind, Function.comp_def] using hcomp
  rw [IndepFun.variance_sum hmem hind]
  calc
    (∑ i ∈ s, variance (X i) (ambientPiMeasure n lambda)) ≤
        ∑ _i ∈ s, ((1 : ℝ) / 4) := by
      apply Finset.sum_le_sum
      intro i hi
      have hbound : ∀ᵐ ω ∂ambientPiMeasure n lambda,
          X i ω ∈ Set.Icc (0 : ℝ) 1 := Filter.Eventually.of_forall fun ω => by
        by_cases h : catalystPoolFamilyOpen ω C (R i) <;>
          simp [X, catalystPoolFamilyIndicator, Set.mem_Icc, h]
      convert variance_le_sq_of_bounded hbound (measurable_of_finite _).aemeasurable
        using 1
      all_goals norm_num
    _ = (s.card : ℝ) / 4 := by
      simp [div_eq_mul_inv]

/-- The variance of one open-family indicator is controlled by its much
smaller closed-family probability.  This retains the decisive factor
`q^(|C||R|)` that the universal `1/4` Bernoulli bound discards. -/
theorem variance_catalystPoolFamilyIndicator_le_closedProbability {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) (R : Finset (Reaction n)) :
    variance (catalystPoolFamilyIndicator C R)
        (ambientPiMeasure n lambda) ≤
      (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * R.card) := by
  let X := catalystPoolFamilyIndicator C R
  have hX : MemLp X 2 (ambientPiMeasure n lambda) :=
    catalystPoolFamilyIndicator_memLp lambda C R
  rw [← variance_const_sub hX.aestronglyMeasurable 1]
  calc
    variance (fun ω => 1 - X ω) (ambientPiMeasure n lambda) ≤
        ∫ ω, (1 - X ω) ^ 2 ∂ambientPiMeasure n lambda := by
      exact variance_le_expectation_sq (by fun_prop)
    _ = ∫ ω, (1 - X ω) ∂ambientPiMeasure n lambda := by
      apply integral_congr_ae
      filter_upwards [] with ω
      by_cases hopen : catalystPoolFamilyOpen ω C R <;>
        simp [X, catalystPoolFamilyIndicator, hopen]
    _ = 1 - ∫ ω, X ω ∂ambientPiMeasure n lambda := by
      rw [integral_sub (integrable_const 1)
        (hX.integrable one_le_two), integral_const]
      simp
    _ = (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
        (C.card * R.card) := by
      rw [show (∫ ω, X ω ∂ambientPiMeasure n lambda) =
          (ambientPiMeasure n lambda).real
            {ω | catalystPoolFamilyOpen ω C R} by
        exact integral_catalystPoolFamilyIndicator_eq_measureReal lambda C R]
      rw [measureReal_catalystPoolFamilyOpen_card]
      ring

/-- Pairwise-disjoint target families inherit the sharp closed-probability
variance bound.  A uniform reaction lower bound `d` makes the full count
variance at most `|s| q^(|C|d)`. -/
theorem variance_sum_catalystPoolFamilyIndicator_le_closedProbability
    {n d : Nat} (lambda : ℝ) (C : Finset (Molecule n))
    {ι : Type*} (s : Finset ι) (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (hcard : ∀ i ∈ s, d ≤ (R i).card) :
    variance (∑ i ∈ s, catalystPoolFamilyIndicator C (R i))
        (ambientPiMeasure n lambda) ≤
      (s.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * d) := by
  classical
  let X : ι → (AmbientCoord n → Prop) → ℝ :=
    fun i => catalystPoolFamilyIndicator C (R i)
  have hmem : ∀ i ∈ s, MemLp (X i) 2 (ambientPiMeasure n lambda) := by
    intro i _
    exact catalystPoolFamilyIndicator_memLp lambda C (R i)
  have hind : Set.Pairwise (↑s : Set ι) fun i j =>
      IndepFun (X i) (X j) (ambientPiMeasure n lambda) := by
    intro i _hi j _hj hij
    have hopen := pairwise_catalystPoolFamilyOpen_indep lambda C R hR hij
    let ind : Prop → ℝ := fun p => if p then 1 else 0
    have hcomp := hopen.comp (measurable_of_finite ind) (measurable_of_finite ind)
    change (fun ω => if catalystPoolFamilyOpen ω C (R i) then (1 : ℝ) else 0) ⟂ᵢ[
        ambientPiMeasure n lambda]
      (fun ω => if catalystPoolFamilyOpen ω C (R j) then (1 : ℝ) else 0)
    simpa [ind, Function.comp_def] using hcomp
  rw [IndepFun.variance_sum hmem hind]
  calc
    (∑ i ∈ s, variance (X i) (ambientPiMeasure n lambda)) ≤
        ∑ _i ∈ s,
          (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
            (C.card * d) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        variance (X i) (ambientPiMeasure n lambda) ≤
            (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (C.card * (R i).card) :=
          variance_catalystPoolFamilyIndicator_le_closedProbability
            lambda C (R i)
        _ ≤ (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (C.card * d) := by
          apply pow_le_pow_of_le_one
          · positivity
          · simpa using (σ (catalysisP n lambda)).2.2
          · exact Nat.mul_le_mul_left C.card (hcard i hi)
    _ = (s.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
          (C.card * d) := by simp

/-- Chebyshev interface for one fixed-pool layer. Once a deterministic lower
bound on the expectation is supplied, this controls the supported-target count
without mutual independence or independence among factor-generation cones. -/
theorem measure_deviation_sum_catalystPoolFamilyIndicator_le {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*} (s : Finset ι)
    (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j)) {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda
        {ω | c ≤ |(∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω -
          ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
            ∂ambientPiMeasure n lambda|} ≤
      ENNReal.ofReal (((s.card : ℝ) / 4) / c ^ 2) := by
  have hmem : MemLp (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) 2
      (ambientPiMeasure n lambda) :=
    memLp_finsetSum' s (fun i _ =>
      catalystPoolFamilyIndicator_memLp lambda C (R i))
  calc
    ambientPiMeasure n lambda {ω | c ≤
        |(∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω -
          ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
            ∂ambientPiMeasure n lambda|} ≤
        ENNReal.ofReal
          (variance (∑ i ∈ s, catalystPoolFamilyIndicator C (R i))
            (ambientPiMeasure n lambda) / c ^ 2) :=
      meas_ge_le_variance_div_sq hmem hc
    _ ≤ ENNReal.ofReal (((s.card : ℝ) / 4) / c ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right
        (variance_sum_catalystPoolFamilyIndicator_le lambda C s R hR)
        (sq_nonneg c)

/-- Lower-tail form: once the fixed-state mean exceeds a threshold by `c`,
the probability that the supported-family count falls below that threshold
has the same Chebyshev bound. -/
theorem measure_sum_catalystPoolFamilyIndicator_le_of_mean_ge {n : Nat}
    (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*} (s : Finset ι)
    (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    {z c : ℝ} (hc : 0 < c)
    (hmean : z + c ≤ ∫ ω,
      (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
        ∂ambientPiMeasure n lambda) :
    ambientPiMeasure n lambda
        {ω | (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω ≤ z} ≤
      ENNReal.ofReal (((s.card : ℝ) / 4) / c ^ 2) := by
  apply le_trans (measure_mono ?_)
    (measure_deviation_sum_catalystPoolFamilyIndicator_le
      lambda C s R hR hc)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [abs_of_nonpos]
  · linarith
  · linarith

/-- Fully explicit fixed-state lower-tail estimate.  If every target has at
least `d` viable reactions against a prospective catalyst pool `C`, then the
number of target families supported by that pool is within any positive
margin `c` of its uniform mean lower bound except with Chebyshev cost
`|s|/(4c²)`. -/
theorem measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub
    {n d : Nat} (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*}
    (s : Finset ι) (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (hcard : ∀ i ∈ s, d ≤ (R i).card) {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda
        {ω | (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω ≤
          (s.card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (C.card * d)) - c} ≤
      ENNReal.ofReal (((s.card : ℝ) / 4) / c ^ 2) := by
  apply measure_sum_catalystPoolFamilyIndicator_le_of_mean_ge
    lambda C s R hR hc
  have hmean :=
    card_mul_one_sub_pow_le_integral_sum_catalystPoolFamilyIndicator
      lambda C s R hcard
  linarith

/-- Sharp lower-tail form retaining the closed-family factor in the variance.
For a macroscopic catalyst pool this is exponentially stronger than the
universal `|s|/(4c^2)` estimate. -/
theorem measure_sum_catalystPoolFamilyIndicator_le_card_mul_one_sub_pow_sub_sharp
    {n d : Nat} (lambda : ℝ) (C : Finset (Molecule n)) {ι : Type*}
    (s : Finset ι) (R : ι → Finset (Reaction n))
    (hR : Pairwise fun i j => Disjoint (R i) (R j))
    (hcard : ∀ i ∈ s, d ≤ (R i).card) {c : ℝ} (hc : 0 < c) :
    ambientPiMeasure n lambda
        {ω | (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω ≤
          (s.card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (C.card * d)) - c} ≤
      ENNReal.ofReal (((s.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * d)) /
          c ^ 2) := by
  have hmem : MemLp (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) 2
      (ambientPiMeasure n lambda) :=
    memLp_finsetSum' s (fun i _ =>
      catalystPoolFamilyIndicator_memLp lambda C (R i))
  have hmean :=
    card_mul_one_sub_pow_le_integral_sum_catalystPoolFamilyIndicator
      lambda C s R hcard
  calc
    ambientPiMeasure n lambda
        {ω | (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω ≤
          (s.card : ℝ) *
            (1 - (toNNReal (σ (catalysisP n lambda)) : ℝ) ^
              (C.card * d)) - c} ≤
        ambientPiMeasure n lambda {ω | c ≤
          |(∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω -
            ∫ ω, (∑ i ∈ s, catalystPoolFamilyIndicator C (R i)) ω
              ∂ambientPiMeasure n lambda|} := by
      apply measure_mono
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [abs_of_nonpos]
      · linarith
      · linarith
    _ ≤ ENNReal.ofReal
        (variance (∑ i ∈ s, catalystPoolFamilyIndicator C (R i))
          (ambientPiMeasure n lambda) / c ^ 2) :=
      meas_ge_le_variance_div_sq hmem hc
    _ ≤ ENNReal.ofReal (((s.card : ℝ) *
        (toNNReal (σ (catalysisP n lambda)) : ℝ) ^ (C.card * d)) /
          c ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      exact div_le_div_of_nonneg_right
        (variance_sum_catalystPoolFamilyIndicator_le_closedProbability
          lambda C s R hR hcard)
        (sq_nonneg c)

end HordijkSteelThreshold

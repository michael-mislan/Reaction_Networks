import proofs.PowerLawSmallRAF.SourceDegreeBandConcentration
import proofs.PowerLawSmallRAF.SourceSplitBlockTail
import proofs.PowerLawSmallRAF.SourceSplitBlocks

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete
open Filter Topology
open scoped BigOperators

/-- Exact product factorization for an iid finite-coordinate event imposed at
every coordinate. -/
theorem finiteProduct_all_coordinates_event
    {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (p : Ω → ℝ) (Good : Ω → Prop) [DecidablePred Good] :
    (∑ cfg : I → Ω,
      if ∀ i, Good (cfg i) then ∏ i, p (cfg i) else 0) =
      (∑ a : Ω, if Good a then p a else 0) ^ Fintype.card I := by
  have hpoint : ∀ cfg : I → Ω,
      (if ∀ i, Good (cfg i) then ∏ i, p (cfg i) else 0) =
        ∏ i, if Good (cfg i) then p (cfg i) else 0 := by
    intro cfg
    by_cases h : ∀ i, Good (cfg i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      simp only [h, if_false]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  simp_rw [hpoint]
  calc
    (∑ cfg : I → Ω, ∏ i, if Good (cfg i) then p (cfg i) else 0) =
        ∏ _i : I, ∑ a : Ω, if Good a then p a else 0 := by
          symm
          exact Fintype.prod_sum (fun _i a => if Good a then p a else 0)
    _ = (∑ a : Ω, if Good a then p a else 0) ^ Fintype.card I := by simp

/-- Exact one-fibre miss mass for an arbitrary degree law whose full-set mass
vanishes.  The latter condition is precisely what lets the source convention
`D = min(K,R)-1` use the range `0, ..., R-1`. -/
theorem finiteDegreeMassMoleculeMiss_eq_coverageMiss
    {J : Type*} [Fintype J] [DecidableEq J]
    (degreeMass : Nat → ℝ) (targets : Finset J)
    (hfull : degreeMass (Fintype.card J) = 0) :
    (∑ A : Finset J,
      if Disjoint A targets then subsetDegreeWeight degreeMass A else 0) =
      coverageMissProfile degreeMass (Fintype.card J) targets.card := by
  classical
  let N := Fintype.card J
  let C := N - targets.card
  have hcardCompl : targetsᶜ.card = C := by
    rw [Finset.card_compl]
  have hfilter :
      (Finset.univ.filter fun A : Finset J => Disjoint A targets) =
        targetsᶜ.powerset := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset]
    exact Finset.subset_compl_iff_disjoint_right.symm
  rw [← Finset.sum_filter, hfilter]
  simp only [subsetDegreeWeight]
  change (∑ A ∈ targetsᶜ.powerset,
    degreeMass A.card / Nat.choose N A.card) = _
  rw [Finset.sum_powerset_apply_card
    (fun d => degreeMass d / Nat.choose N d)]
  rw [hcardCompl]
  have hCN : C ≤ N := Nat.sub_le _ _
  let f : Nat → ℝ := fun d =>
    degreeMass d * ((Nat.choose C d : ℝ) / Nat.choose N d)
  have hterms : ∀ d ∈ Finset.range (C + 1),
      Nat.choose C d • (degreeMass d / Nat.choose N d) = f d := by
    intro d hd
    have hdC : d ≤ C := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
    have hdN : d ≤ N := hdC.trans hCN
    have hchoose : (Nat.choose N d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hdN).ne'
    simp only [nsmul_eq_mul, f]
    field_simp
  rw [Finset.sum_congr rfl hterms]
  have hextend :
      (∑ d ∈ Finset.range (C + 1), f d) =
        ∑ d ∈ Finset.range (N + 1), f d := by
    apply Finset.sum_subset
    · exact Finset.range_mono (Nat.succ_le_succ hCN)
    · intro d hdN hdnotC
      have hdC : C < d := by
        simpa only [Finset.mem_range, not_lt] using hdnotC
      simp [f, Nat.choose_eq_zero_of_lt hdC]
  rw [hextend, Finset.sum_range_succ]
  have hfN : f N = 0 := by
    have hfullN : degreeMass N = 0 := by simpa only [N] using hfull
    dsimp only [f]
    rw [hfullN, zero_mul]
  rw [hfN, add_zero]
  change (∑ d ∈ Finset.range N,
      degreeMass d *
        ((Nat.choose (N - targets.card) d : ℝ) / Nat.choose N d)) = _
  rfl

/-- Capped-Zipf degree mass retained inside a half-open band. -/
noncomputable def sourceBandDegreeMass
    (a : ℝ) (n L U d : Nat) : ℝ :=
  if L ≤ d ∧ d < U then
    cappedZipfDegreeMass a (sourceReactionCount n) d
  else 0

/-- Analytic one-molecule probability of both lying in the degree band and
hitting one of `M` prescribed channels. -/
noncomputable def sourceBandGatewayHit
    (a : ℝ) (n L U M : Nat) : ℝ :=
  (∑ d ∈ Finset.range (sourceReactionCount n),
      sourceBandDegreeMass a n L U d) -
    coverageMissProfile (sourceBandDegreeMass a n L U)
      (sourceReactionCount n) M

theorem sourceBandGatewayHit_eq_sum
    (a : ℝ) (n L U M : Nat) :
    sourceBandGatewayHit a n L U M =
      ∑ d ∈ Finset.range (sourceReactionCount n),
        sourceBandDegreeMass a n L U d *
          (1 - hypergeometricGatewayMiss (sourceReactionCount n) M d) := by
  rw [sourceBandGatewayHit, coverageMissProfile]
  simp_rw [degreeMissProbability_eq_gatewayMiss]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem sourceTruncatedBandMean_eq_bandDegreeSum
    (a : ℝ) (n L U : Nat) (hn : 2 ≤ n) :
    sourceTruncatedBandMean a n L U =
      ∑ d ∈ Finset.range (sourceReactionCount n),
        sourceBandDegreeMass a n L U d * (d : ℝ) := by
  rw [sourceTruncatedBandMean_eq_degreeSum a n L U hn,
    Finset.sum_range_succ]
  have htop :
      cappedZipfDegreeMass a (sourceReactionCount n) (sourceReactionCount n) *
          (if L ≤ sourceReactionCount n ∧ sourceReactionCount n < U then
            (sourceReactionCount n : ℝ) else 0) = 0 := by
    simp [cappedZipfDegreeMass]
  rw [htop, add_zero]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hband : L ≤ d ∧ d < U <;>
    simp [sourceBandDegreeMass, hband]

/-- Finite hypergeometric lower bound using only the first moment carried by
the retained band.  The quadratic correction is uniform because every
selected degree is below `U`. -/
theorem sourceBandGatewayHit_ge_truncatedBandMean
    (a : ℝ) (n L U M : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    (hM0 : 0 < M) (hMR : M ≤ sourceReactionCount n)
    :
    ((M : ℝ) / (sourceReactionCount n : ℝ) -
        ((M : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 * (U : ℝ)) *
        sourceTruncatedBandMean a n L U ≤
      sourceBandGatewayHit a n L U M := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hpoint : ∀ d ∈ Finset.range (sourceReactionCount n),
      ((M : ℝ) / (sourceReactionCount n : ℝ) -
          ((M : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 * (U : ℝ)) *
          (sourceBandDegreeMass a n L U d * (d : ℝ)) ≤
        sourceBandDegreeMass a n L U d *
          (1 - hypergeometricGatewayMiss (sourceReactionCount n) M d) := by
    intro d hd
    by_cases hband : L ≤ d ∧ d < U
    · rw [sourceBandDegreeMass, if_pos hband]
      have hdU : d ≤ U := hband.2.le
      have hdR : d < sourceReactionCount n := Finset.mem_range.mp hd
      have hmass : 0 ≤ cappedZipfDegreeMass a (sourceReactionCount n) d :=
        cappedZipfDegreeMass_nonneg a (sourceReactionCount n) d hzpos
      have henv := (hypergeometricGatewayHit_envelope
        (sourceReactionCount n) M d hM0 hMR hdR).1
      have hd0 : (0 : ℝ) ≤ d := by positivity
      have hdUreal : (d : ℝ) ≤ U := by exact_mod_cast hdU
      have hsq : (d : ℝ) ^ 2 ≤ (U : ℝ) * (d : ℝ) := by nlinarith
      have hinner :
          ((M : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
                  (U : ℝ)) * (d : ℝ) ≤
            (M : ℝ) * (d : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) * (d : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 := by
        have hq : 0 ≤ ((M : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 := sq_nonneg _
        calc
          ((M : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
                  (U : ℝ)) * (d : ℝ) =
            (M : ℝ) * (d : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
                  ((U : ℝ) * (d : ℝ)) := by ring
          _ ≤ (M : ℝ) * (d : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 *
                  (d : ℝ) ^ 2 := by nlinarith
          _ = (M : ℝ) * (d : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) * (d : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 := by ring
      calc
        ((M : ℝ) / (sourceReactionCount n : ℝ) -
            ((M : ℝ) /
              ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 * (U : ℝ)) *
            (cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ)) =
          cappedZipfDegreeMass a (sourceReactionCount n) d *
            (((M : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2 * (U : ℝ)) *
                (d : ℝ)) := by ring
        _ ≤ cappedZipfDegreeMass a (sourceReactionCount n) d *
            ((M : ℝ) * (d : ℝ) / (sourceReactionCount n : ℝ) -
              ((M : ℝ) * (d : ℝ) /
                ((sourceReactionCount n - M + 1 : Nat) : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hinner hmass
        _ ≤ cappedZipfDegreeMass a (sourceReactionCount n) d *
            (1 - hypergeometricGatewayMiss (sourceReactionCount n) M d) :=
          mul_le_mul_of_nonneg_left henv hmass
    · simp [sourceBandDegreeMass, hband]
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hsum
  rw [sourceTruncatedBandMean_eq_bandDegreeSum a n L U (by omega),
    sourceBandGatewayHit_eq_sum]
  exact hsum

/-- The elementary union bound gives the matching first-moment upper bound
for a band-restricted fibre. -/
theorem sourceBandGatewayHit_le_truncatedBandMean
    (a : ℝ) (n L U M : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    (hM0 : 0 < M) (hMR : M ≤ sourceReactionCount n) :
    sourceBandGatewayHit a n L U M ≤
      ((M : ℝ) /
        ((sourceReactionCount n - M + 1 : Nat) : ℝ)) *
        sourceTruncatedBandMean a n L U := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [sourceBandGatewayHit_eq_sum,
    sourceTruncatedBandMean_eq_bandDegreeSum a n L U (by omega),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  by_cases hband : L ≤ d ∧ d < U
  · rw [sourceBandDegreeMass, if_pos hband]
    have hdR : d < sourceReactionCount n := Finset.mem_range.mp hd
    have hmass : 0 ≤ cappedZipfDegreeMass a (sourceReactionCount n) d :=
      cappedZipfDegreeMass_nonneg a (sourceReactionCount n) d hzpos
    have henv := (hypergeometricGatewayHit_envelope
      (sourceReactionCount n) M d hM0 hMR hdR).2
    calc
      cappedZipfDegreeMass a (sourceReactionCount n) d *
          (1 - hypergeometricGatewayMiss (sourceReactionCount n) M d) ≤
        cappedZipfDegreeMass a (sourceReactionCount n) d *
          ((M : ℝ) * (d : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) :=
        mul_le_mul_of_nonneg_left henv hmass
      _ = (M : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ) *
          (cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ)) := by
        ring
  · simp [sourceBandDegreeMass, hband]

/-- For the polynomial upper cutoff, the same vanishing finite-population
correction used by the full catalogue controls the selected band uniformly
over every split block of size at most `n`. -/
theorem sourceBand_truncated_hit_uniform_lower
    (a : ℝ) {n M L : Nat} (hn : 16 ≤ n) (ha : 1 < a)
    (hM0 : 0 < M) (hMn : M ≤ n) :
    ((M : ℝ) / (sourceReactionCount n : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        sourceTruncatedBandMean a n L (sourcePolynomialCutoff n - 1) ≤
      sourceBandGatewayHit a n L (sourcePolynomialCutoff n - 1) M := by
  let R := sourceReactionCount n
  let U := sourcePolynomialCutoff n - 1
  have hMR : M ≤ R := by
    have hpoly : n ^ 4 ≤ R :=
      (fourth_pow_le_two_pow hn).trans
        (sourceReactionCount_bounds (by omega)).1
    exact hMn.trans (by
      have : n ≤ n ^ 4 := by
        simpa only [pow_one] using
          (Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ 4))
      exact this.trans hpoly)
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hmean0 : 0 ≤ sourceTruncatedBandMean a n L U := by
    rw [sourceTruncatedBandMean_eq_bandDegreeSum a n L U (by omega)]
    apply Finset.sum_nonneg
    intro d hd
    by_cases hband : L ≤ d ∧ d < U
    · rw [sourceBandDegreeMass, if_pos hband]
      exact mul_nonneg
        (cappedZipfDegreeMass_nonneg a R d hzpos) (by positivity)
    · simp [sourceBandDegreeMass, hband]
  have herr := source_split_relative_error_le_envelope hn hM0 hMn
  have hfinite := sourceBandGatewayHit_ge_truncatedBandMean
    a n L U M ha (by omega) hM0 hMR
  have hR0 : (0 : ℝ) < R := by
    exact_mod_cast (hM0.trans_le hMR)
  have hD0 : (0 : ℝ) < ((R - M + 1 : Nat) : ℝ) := by
    exact_mod_cast (by omega : 0 < R - M + 1)
  calc
    ((M : ℝ) / (sourceReactionCount n : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        sourceTruncatedBandMean a n L (sourcePolynomialCutoff n - 1) =
      ((M : ℝ) / (R : ℝ)) *
        (1 - sourceSplitUniformErrorEnvelope n) *
        sourceTruncatedBandMean a n L U := by rfl
    _ ≤ ((M : ℝ) / (R : ℝ)) *
        (1 - ((M : ℝ) * (R : ℝ) * (U : ℝ) /
          ((R - M + 1 : Nat) : ℝ) ^ 2)) *
        sourceTruncatedBandMean a n L U := by
          have hfac : 0 ≤ (M : ℝ) / (R : ℝ) := by positivity
          gcongr
    _ = ((M : ℝ) / (R : ℝ) -
        ((M : ℝ) / ((R - M + 1 : Nat) : ℝ)) ^ 2 * (U : ℝ)) *
        sourceTruncatedBandMean a n L U := by
          field_simp
    _ ≤ sourceBandGatewayHit a n L U M := hfinite

/-- Scaled version of the uniform band-hit bound, ready for exponential miss
estimates after inserting the limiting band density. -/
theorem sourceBand_uniform_rate_le_scaled_hit
    (a : ℝ) {n M L : Nat} (hn : 16 ≤ n) (ha : 1 < a)
    (hM0 : 0 < M) (hMn : M ≤ n) :
    (M : ℝ) * (1 - sourceSplitUniformErrorEnvelope n) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean a n L (sourcePolynomialCutoff n - 1)) ≤
      (sourceMoleculeCount n : ℝ) *
        sourceBandGatewayHit a n L (sourcePolynomialCutoff n - 1) M := by
  have h := sourceBand_truncated_hit_uniform_lower
    a hn ha hM0 hMn (L := L)
  have hX0 : (0 : ℝ) ≤ sourceMoleculeCount n := by positivity
  have hm := mul_le_mul_of_nonneg_left h hX0
  convert hm using 1
  all_goals ring

/-- Any strict lower bound on the limiting retained band density becomes a
uniform exponential rate for all split blocks of admissible word length. -/
theorem eventually_sourceBand_scaled_hit_ge
    (lam : ℝ) (hlam : 0 < lam) (L : Nat → Nat) (q q₀ : ℝ)
    (hdensity : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
          (sourcePolynomialCutoff n - 1)) atTop (𝓝 q))
    (hq₀ : q₀ < q) :
    ∀ᶠ n : Nat in atTop, ∀ M : Nat, 0 < M → M ≤ n →
      (M : ℝ) * q₀ ≤
        (sourceMoleculeCount n : ℝ) *
          sourceBandGatewayHit (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1) M := by
  have hone : Tendsto (fun n : Nat =>
      1 - sourceSplitUniformErrorEnvelope n) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub sourceSplitUniformErrorEnvelope_tendsto_zero)
  have hrate : Tendsto (fun n : Nat =>
      (1 - sourceSplitUniformErrorEnvelope n) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1))) atTop (𝓝 q) := by
    simpa only [one_mul] using hone.mul hdensity
  have hlower : ∀ᶠ n : Nat in atTop,
      q₀ < (1 - sourceSplitUniformErrorEnvelope n) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1)) :=
    hrate (Ioi_mem_nhds hq₀)
  have ha : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [hlower, ha, eventually_ge_atTop 16] with n hnrate han hn
  intro M hM0 hMn
  have hfinite := sourceBand_uniform_rate_le_scaled_hit
    (calibrationExponent lam hlam n) hn han hM0 hMn (L := L n)
  have hMq : (M : ℝ) * q₀ ≤
      (M : ℝ) * ((1 - sourceSplitUniformErrorEnvelope n) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1))) := by
    exact mul_le_mul_of_nonneg_left hnrate.le (by positivity)
  exact hMq.trans (by simpa only [mul_assoc] using hfinite)

/-- For a fixed nonempty target, the band-restricted hit probability has the
same first-order limit as its retained degree mass. -/
theorem sourceBand_scaled_hit_tendsto
    (lam : ℝ) (hlam : 0 < lam) (L : Nat → Nat) (q : ℝ)
    (hdensity : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
          (sourcePolynomialCutoff n - 1)) atTop (𝓝 q))
    (M : Nat) (hM0 : 0 < M) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        sourceBandGatewayHit (calibrationExponent lam hlam n) n (L n)
          (sourcePolynomialCutoff n - 1) M) atTop
      (𝓝 ((M : ℝ) * q)) := by
  have hone : Tendsto (fun n : Nat =>
      1 - sourceSplitUniformErrorEnvelope n) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds.sub sourceSplitUniformErrorEnvelope_tendsto_zero)
  have hlower : Tendsto (fun n : Nat =>
      (M : ℝ) * (1 - sourceSplitUniformErrorEnvelope n) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1))) atTop
      (𝓝 ((M : ℝ) * q)) := by
    simpa only [mul_one, mul_assoc] using
      (tendsto_const_nhds.mul hone).mul hdensity
  have hratio := sourceReactionCount_div_gatewayDenominator_tendsto_one M hM0
  have hupper : Tendsto (fun n : Nat =>
      (M : ℝ) *
        ((sourceReactionCount n : ℝ) /
          ((sourceReactionCount n - M + 1 : Nat) : ℝ)) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1))) atTop
      (𝓝 ((M : ℝ) * q)) := by
    simpa only [mul_one, mul_assoc] using
      (tendsto_const_nhds.mul hratio).mul hdensity
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · have ha : ∀ᶠ n : Nat in atTop,
        1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [eventually_ge_atTop 16, eventually_ge_atTop M, ha] with
      n hn hMn han
    exact sourceBand_uniform_rate_le_scaled_hit
      (calibrationExponent lam hlam n) hn han hM0 hMn (L := L n)
  · have ha : ∀ᶠ n : Nat in atTop,
        1 < calibrationExponent lam hlam n :=
      (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
    filter_upwards [eventually_ge_atTop 16, eventually_ge_atTop M, ha] with
      n hn hMn han
    have hR : M ≤ sourceReactionCount n := by
      have hpoly : n ^ 4 ≤ sourceReactionCount n :=
        (fourth_pow_le_two_pow hn).trans
          (sourceReactionCount_bounds (by omega)).1
      exact hMn.trans (by
        have : n ≤ n ^ 4 := by
          simpa only [pow_one] using
            (Nat.pow_le_pow_right (by omega : 0 < n) (by omega : 1 ≤ 4))
        exact this.trans hpoly)
    have h := sourceBandGatewayHit_le_truncatedBandMean
      (calibrationExponent lam hlam n) n (L n)
        (sourcePolynomialCutoff n - 1) M han (by omega) hM0 hR
    have hX0 : (0 : ℝ) ≤ sourceMoleculeCount n := by positivity
    have hm := mul_le_mul_of_nonneg_left h hX0
    have hR0 : (sourceReactionCount n : ℝ) ≠ 0 := by
      rw [sourceReactionCount]
      positivity
    calc
      (sourceMoleculeCount n : ℝ) *
          sourceBandGatewayHit (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1) M ≤
        (sourceMoleculeCount n : ℝ) *
          ((M : ℝ) / ((sourceReactionCount n - M + 1 : Nat) : ℝ) *
            sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
              (sourcePolynomialCutoff n - 1)) := hm
      _ = (M : ℝ) *
          ((sourceReactionCount n : ℝ) /
            ((sourceReactionCount n - M + 1 : Nat) : ℝ)) *
          ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
            sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
              (sourcePolynomialCutoff n - 1)) := by
        field_simp [hR0]

/-- One molecule's exact probability of being selected by the degree band
and hitting a prescribed target set. -/
noncomputable def sourceBandTargetHitMass
    (a : ℝ) (n L U : Nat) (targets : Finset (Reaction n)) : ℝ :=
  ∑ A : Finset (Reaction n),
    if L ≤ A.card ∧ A.card < U ∧ ¬ Disjoint A targets then
      subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
    else 0

/-- The selected-band hit probability depends on a target only through its
cardinality and is exactly the band-restricted hypergeometric hit profile. -/
theorem sourceBandTargetHitMass_eq_gatewayHit
    (a : ℝ) (n L U : Nat) (targets : Finset (Reaction n))
    (hn : 2 ≤ n) :
    sourceBandTargetHitMass a n L U targets =
      sourceBandGatewayHit a n L U targets.card := by
  classical
  let q := sourceBandDegreeMass a n L U
  let w : Finset (Reaction n) → ℝ := fun A => subsetDegreeWeight q A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) hn
  have hfull : q (Fintype.card (Reaction n)) = 0 := by
    simp only [q, sourceBandDegreeMass, hcard]
    by_cases hband : L ≤ sourceReactionCount n ∧ sourceReactionCount n < U
    · simp only [if_pos hband]
      simp [cappedZipfDegreeMass]
    · simp [hband]
  have hmiss :
      (∑ A : Finset (Reaction n), if Disjoint A targets then w A else 0) =
        coverageMissProfile q (Fintype.card (Reaction n)) targets.card := by
    exact finiteDegreeMassMoleculeMiss_eq_coverageMiss q targets hfull
  rw [hcard] at hmiss
  have htotal0 :=
    sum_subsetDegreeWeight_eq_mass_sum (J := Reaction n) q
  have hfullR : q (sourceReactionCount n) = 0 := by
    rw [← hcard]
    exact hfull
  rw [hcard, Finset.sum_range_succ, hfullR, add_zero] at htotal0
  have htotal : (∑ A : Finset (Reaction n), w A) =
      ∑ d ∈ Finset.range (sourceReactionCount n), q d := by
    simpa only [w] using htotal0
  have hsplit :
      (∑ A : Finset (Reaction n), if Disjoint A targets then w A else 0) +
        (∑ A : Finset (Reaction n), if ¬ Disjoint A targets then w A else 0) =
          ∑ A : Finset (Reaction n), w A := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hdis : Disjoint A targets <;> simp [hdis]
  have hhit : sourceBandTargetHitMass a n L U targets =
      ∑ A : Finset (Reaction n), if ¬ Disjoint A targets then w A else 0 := by
    rw [sourceBandTargetHitMass]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hband : L ≤ A.card ∧ A.card < U <;>
      by_cases hdis : Disjoint A targets <;>
        simp [w, q, sourceBandDegreeMass, subsetDegreeWeight, hband, hdis]
  rw [hhit, sourceBandGatewayHit]
  dsimp only [q] at hmiss htotal ⊢
  linarith

theorem sourceBandTargetHitMass_nonneg_le_one
    (a : ℝ) (n L U : Nat) (targets : Finset (Reaction n))
    (ha : 1 < a) (hn : 4 ≤ n) :
    0 ≤ sourceBandTargetHitMass a n L U targets ∧
      sourceBandTargetHitMass a n L U targets ≤ 1 := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have htotal : (∑ A : Finset (Reaction n),
      subsetDegreeWeight
        (cappedZipfDegreeMass a (sourceReactionCount n)) A) = 1 := by
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  constructor
  · rw [sourceBandTargetHitMass]
    apply Finset.sum_nonneg
    intro A hA
    split_ifs
    · exact subsetDegreeWeight_nonneg _
        (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) A
    · exact le_rfl
  · rw [sourceBandTargetHitMass]
    calc
      (∑ A : Finset (Reaction n),
        if L ≤ A.card ∧ A.card < U ∧ ¬ Disjoint A targets then
          subsetDegreeWeight
            (cappedZipfDegreeMass a (sourceReactionCount n)) A else 0) ≤
        ∑ A : Finset (Reaction n),
          subsetDegreeWeight
            (cappedZipfDegreeMass a (sourceReactionCount n)) A := by
              apply Finset.sum_le_sum
              intro A hA
              split_ifs
              · exact le_rfl
              · exact subsetDegreeWeight_nonneg _
                  (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) A
      _ = 1 := htotal

/-- Exact source mass that no degree-band molecule hits `targets`. -/
noncomputable def sourceBandTargetJointMissWeight
    (a : ℝ) (n L U : Nat) (targets : Finset (Reaction n)) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if ∀ y : Molecule n,
        ¬ (L ≤ (config y).card ∧ (config y).card < U ∧
          ¬ Disjoint (config y) targets) then
      sourcePowerLawConfigWeight a n config
    else 0

set_option maxHeartbeats 800000 in
/-- Selecting catalysts by fibre cardinality does not disturb conditional
uniformity: the joint miss mass remains an exact iid power. -/
theorem sourceBandTargetJointMissWeight_eq_pow
    (a : ℝ) (n L U : Nat) (targets : Finset (Reaction n))
    (ha : 1 < a) (hn : 4 ≤ n) :
    sourceBandTargetJointMissWeight a n L U targets =
      (1 - sourceBandTargetHitMass a n L U targets) ^
        sourceMoleculeCount n := by
  let p : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  let Good : Finset (Reaction n) → Prop := fun A =>
    ¬ (L ≤ A.card ∧ A.card < U ∧ ¬ Disjoint A targets)
  letI : DecidablePred Good := Classical.decPred _
  have hprod := finiteProduct_all_coordinates_event
    (I := Molecule n) p Good
  rw [card_binaryMolecule_eq_sourceMoleculeCount n] at hprod
  rw [sourceBandTargetJointMissWeight]
  simp only [sourcePowerLawConfigWeight]
  change (∑ config : SourceMoleculeFibreConfig n,
      if ∀ y, Good (config y) then ∏ y, p (config y) else 0) = _
  rw [hprod]
  congr 1
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hp.trans (sourceReactionCount_bounds hn).1
  have hpSum : ∑ A, p A = 1 := by
    dsimp [p]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Reaction n))) Good p
  have hgood : (∑ A, if Good A then p A else 0) =
      ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter Good,
        p A := by rw [Finset.sum_filter]
  have hbad : sourceBandTargetHitMass a n L U targets =
      ∑ A ∈ (Finset.univ : Finset (Finset (Reaction n))).filter
        (fun A => ¬ Good A), p A := by
    rw [sourceBandTargetHitMass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro A hA
    simp [Good, p]
  rw [hpSum] at hpartition
  rw [hgood, hbad]
  linarith

/-- Any moving family of fixed-cardinality targets has the expected Poisson
miss limit under the retained degree band. -/
theorem sourceBandTargetJointMissWeight_tendsto
    (lam : ℝ) (hlam : 0 < lam) (L : Nat → Nat) (q : ℝ) (hq : 0 < q)
    (hdensity : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
          (sourcePolynomialCutoff n - 1)) atTop (𝓝 q))
    (targets : ∀ n : Nat, Finset (Reaction n)) (M : Nat) (hM0 : 0 < M)
    (hcard : ∀ᶠ n : Nat in atTop, (targets n).card = M) :
    Tendsto (fun n : Nat =>
      sourceBandTargetJointMissWeight (calibrationExponent lam hlam n) n
        (L n) (sourcePolynomialCutoff n - 1) (targets n)) atTop
      (𝓝 (Real.exp (-((M : ℝ) * q)))) := by
  let p : Nat → ℝ := fun n =>
    sourceBandTargetHitMass (calibrationExponent lam hlam n) n
      (L n) (sourcePolynomialCutoff n - 1) (targets n)
  have hNp : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ) * p n)
      atTop (𝓝 ((M : ℝ) * q)) := by
    have h := sourceBand_scaled_hit_tendsto lam hlam L q hdensity M hM0
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2, hcard] with n hn hncard
    dsimp only [p]
    rw [sourceBandTargetHitMass_eq_gatewayHit _ _ _ _ _ hn, hncard]
  have hXtop : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hp : Tendsto p atTop (𝓝 0) := by
    have h := hNp.mul hXtop.inv_tendsto_atTop
    have h' : Tendsto (fun n : Nat =>
        ((sourceMoleculeCount n : ℝ) * p n) *
          (sourceMoleculeCount n : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hn
    field_simp
  have htheta : 0 < (M : ℝ) * q := mul_pos (by exact_mod_cast hM0) hq
  have hprodpos : ∀ᶠ n : Nat in atTop,
      0 < (sourceMoleculeCount n : ℝ) * p n :=
    hNp (Ioi_mem_nhds htheta)
  have hpne : ∀ᶠ n : Nat in atTop, p n ≠ 0 := by
    filter_upwards [hprodpos] with n hn hzero
    rw [hzero, mul_zero] at hn
    exact (lt_irrefl 0 hn)
  have hplt : ∀ᶠ n : Nat in atTop, p n < 1 :=
    hp (Iio_mem_nhds one_pos)
  have hbin := binomialNoHit_tendsto_exp_neg sourceMoleculeCount p
    ((M : ℝ) * q) hp hpne hplt hNp
  apply hbin.congr'
  have ha : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [eventually_ge_atTop 4, ha] with n hn han
  symm
  exact sourceBandTargetJointMissWeight_eq_pow
    (calibrationExponent lam hlam n) n (L n)
      (sourcePolynomialCutoff n - 1) (targets n) han hn

/-- Once the limiting band density dominates `q₀`, every source split block
of size at most `n` has exponentially small exact joint miss mass, uniformly
in the identity of its reaction channels. -/
theorem eventually_sourceBandTargetJointMissWeight_le_exp
    (lam : ℝ) (hlam : 0 < lam) (L : Nat → Nat) (q q₀ : ℝ)
    (hdensity : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n) n (L n)
          (sourcePolynomialCutoff n - 1)) atTop (𝓝 q))
    (hq₀ : q₀ < q) :
    ∀ᶠ n : Nat in atTop, ∀ targets : Finset (Reaction n),
      0 < targets.card → targets.card ≤ n →
      sourceBandTargetJointMissWeight (calibrationExponent lam hlam n) n
          (L n) (sourcePolynomialCutoff n - 1) targets ≤
        Real.exp (-(targets.card : ℝ) * q₀) := by
  have hscaled := eventually_sourceBand_scaled_hit_ge
    lam hlam L q q₀ hdensity hq₀
  have ha : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  filter_upwards [hscaled, ha, eventually_ge_atTop 16] with n hnscaled han hn
  intro targets htargets0 htargetsn
  let p := sourceBandTargetHitMass (calibrationExponent lam hlam n) n
    (L n) (sourcePolynomialCutoff n - 1) targets
  have hp1 : p ≤ 1 :=
    (sourceBandTargetHitMass_nonneg_le_one
      (calibrationExponent lam hlam n) n (L n)
        (sourcePolynomialCutoff n - 1) targets han (by omega)).2
  have hrate := hnscaled targets.card htargets0 htargetsn
  rw [← sourceBandTargetHitMass_eq_gatewayHit
    (calibrationExponent lam hlam n) n (L n)
      (sourcePolynomialCutoff n - 1) targets (by omega)] at hrate
  calc
    sourceBandTargetJointMissWeight (calibrationExponent lam hlam n) n
        (L n) (sourcePolynomialCutoff n - 1) targets =
      (1 - p) ^ sourceMoleculeCount n := by
        exact sourceBandTargetJointMissWeight_eq_pow
          (calibrationExponent lam hlam n) n (L n)
            (sourcePolynomialCutoff n - 1) targets han (by omega)
    _ ≤ Real.exp ((sourceMoleculeCount n : ℝ) * (-p)) :=
      one_sub_pow_le_exp_neg_mul p (sourceMoleculeCount n) hp1
    _ ≤ Real.exp (-(targets.card : ℝ) * q₀) := by
      apply Real.exp_le_exp.mpr
      dsimp only [p] at hrate ⊢
      nlinarith

end PowerLawSmallRAF

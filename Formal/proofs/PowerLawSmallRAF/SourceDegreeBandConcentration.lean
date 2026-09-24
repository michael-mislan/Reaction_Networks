import proofs.PowerLawSmallRAF.FiniteProductVariance
import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability
import proofs.PowerLawSmallRAF.MovingBandMass

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete
open Filter Topology
open scoped BigOperators

/-- Push a uniform-conditional subset law through any function of the subset
cardinality.  The binomial multiplicity cancels exactly. -/
theorem sum_subsetDegreeWeight_mul_cardFunction_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    (degreeMass : Nat → ℝ) (f : Nat → ℝ) :
    (∑ A : Finset J, subsetDegreeWeight degreeMass A * f A.card) =
      ∑ d ∈ Finset.range (Fintype.card J + 1), degreeMass d * f d := by
  rw [← Finset.powerset_univ]
  simp only [subsetDegreeWeight]
  rw [Finset.sum_powerset_apply_card
    (fun d => degreeMass d / Nat.choose (Fintype.card J) d * f d)]
  simp only [Finset.card_univ]
  apply Finset.sum_congr rfl
  intro d hd
  have hdJ : d ≤ Fintype.card J := by
    have hdlt := Finset.mem_range.mp hd
    omega
  have hchooseNat : 0 < Nat.choose (Fintype.card J) d :=
    Nat.choose_pos hdJ
  have hchoose : (Nat.choose (Fintype.card J) d : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  simp only [nsmul_eq_mul]
  field_simp

/-- The retained degree carried by one fibre in a half-open degree band. -/
def truncatedBandValue {J : Type*} (L U : Nat) (A : Finset J) : ℝ :=
  if L ≤ A.card ∧ A.card < U then A.card else 0

theorem truncatedBandValue_nonneg {J : Type*} (L U : Nat) (A : Finset J) :
    0 ≤ truncatedBandValue L U A := by
  by_cases h : L ≤ A.card ∧ A.card < U
  · simp [truncatedBandValue, h]
  · simp [truncatedBandValue, h]

theorem truncatedBandValue_le {J : Type*} (L U : Nat) (A : Finset J) :
    truncatedBandValue L U A ≤ U := by
  by_cases h : L ≤ A.card ∧ A.card < U
  · simp only [truncatedBandValue, if_pos h]
    exact_mod_cast h.2.le
  · simp [truncatedBandValue, h]

/-- Exact one-fibre mean retained in a source degree band. -/
noncomputable def sourceTruncatedBandMean
    (a : ℝ) (n L U : Nat) : ℝ :=
  ∑ A : Finset (Reaction n),
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A *
      truncatedBandValue L U A

/-- The source one-fibre band mean is exactly the capped-Zipf degree sum.
This is the finite bridge from the subset-valued source law to the analytic
degree variable. -/
theorem sourceTruncatedBandMean_eq_degreeSum
    (a : ℝ) (n L U : Nat) (hn : 2 ≤ n) :
    sourceTruncatedBandMean a n L U =
      ∑ d ∈ Finset.range (sourceReactionCount n + 1),
        cappedZipfDegreeMass a (sourceReactionCount n) d *
          (if L ≤ d ∧ d < U then (d : ℝ) else 0) := by
  have h := sum_subsetDegreeWeight_mul_cardFunction_eq
    (J := Reaction n) (cappedZipfDegreeMass a (sourceReactionCount n))
    (fun d => if L ≤ d ∧ d < U then (d : ℝ) else 0)
  rw [card_binaryReaction_eq_sourceReactionCount hn] at h
  simpa only [sourceTruncatedBandMean, truncatedBandValue] using h

theorem sourceTruncatedBandMean_eq_Ico
    (a : ℝ) (n L U : Nat) (hn : 2 ≤ n)
    (hU : U ≤ sourceReactionCount n + 1) :
    sourceTruncatedBandMean a n L U =
      ∑ d ∈ Finset.Ico L U,
        cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ) := by
  rw [sourceTruncatedBandMean_eq_degreeSum a n L U hn]
  calc
    (∑ d ∈ Finset.range (sourceReactionCount n + 1),
        cappedZipfDegreeMass a (sourceReactionCount n) d *
          (if L ≤ d ∧ d < U then (d : ℝ) else 0)) =
        ∑ d ∈ Finset.range (sourceReactionCount n + 1),
          if L ≤ d ∧ d < U then
            cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ)
          else 0 := by
            apply Finset.sum_congr rfl
            intro d hd
            by_cases h : L ≤ d ∧ d < U <;> simp [h]
    _ = ∑ d ∈ (Finset.range (sourceReactionCount n + 1)).filter
          (fun d => L ≤ d ∧ d < U),
          cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ) := by
            rw [Finset.sum_filter]
    _ = ∑ d ∈ Finset.Ico L U,
          cappedZipfDegreeMass a (sourceReactionCount n) d * (d : ℝ) := by
            congr 1
            ext d
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
            omega

/-- Subtracting two exact high-tail numerators cancels the capped atom and
leaves precisely the intervening uncapped degree band. -/
theorem windowHighNumerator_sub_eq_band
    (a : ℝ) (R L U : Nat) (hL : 1 ≤ L) (hLU : L ≤ U) :
    windowHighNumerator a R (L + 1) -
        windowHighNumerator a R (U + 1) =
      ∑ k ∈ Finset.Ico (L + 1) (U + 1),
        (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a)) := by
  rw [windowHighNumerator, windowHighNumerator]
  dsimp only [windowPartialNumerator]
  rw [← Finset.sum_Ico_consecutive
    (fun k : Nat => (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a)))
    (by omega : 2 ≤ L + 1) (by omega : L + 1 ≤ U + 1)]
  ring

theorem cappedZipfDegreeMass_Ico_eq_shiftedBand
    (a : ℝ) (R L U : Nat) (hLU : L ≤ U) (hUR : U < R) :
    (∑ d ∈ Finset.Ico L U, cappedZipfDegreeMass a R d * (d : ℝ)) =
      (∑ k ∈ Finset.Ico (L + 1) (U + 1),
        (((k - 1 : Nat) : ℝ) * (k : ℝ) ^ (-a))) /
          zipfNormalizer a := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  rw [show U + 1 - (L + 1) = U - L by omega, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i < U - L := Finset.mem_range.mp hi
  have hdegree : L + i + 1 < R := by omega
  rw [cappedZipfDegreeMass, if_pos hdegree]
  rw [show L + 1 + i - 1 = L + i by omega]
  push_cast
  ring

/-- Exact analytic form of the source one-fibre degree retained between two
uncapped thresholds. -/
theorem sourceTruncatedBandMean_eq_highNumerator_sub
    (a : ℝ) (n L U : Nat) (hn : 2 ≤ n) (hL : 1 ≤ L)
    (hLU : L ≤ U) (hUR : U < sourceReactionCount n) :
    sourceTruncatedBandMean a n L U =
      (windowHighNumerator a (sourceReactionCount n) (L + 1) -
        windowHighNumerator a (sourceReactionCount n) (U + 1)) /
          zipfNormalizer a := by
  rw [sourceTruncatedBandMean_eq_Ico a n L U hn (by omega)]
  rw [cappedZipfDegreeMass_Ico_eq_shiftedBand a
    (sourceReactionCount n) L U hLU hUR]
  rw [windowHighNumerator_sub_eq_band a (sourceReactionCount n) L U hL hLU]

/-- The expected source density of a truncated degree band has the same
calibrated limit as its lower high-tail threshold whenever the discarded
upper tail has full source exponential rate. -/
theorem sourceExpectedTruncatedBandDensity_tendsto
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (L U : Nat → Nat)
    (hLlog : Tendsto (fun n : Nat => Real.log ((L n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 ((1 - c) * Real.log 2)))
    (hUlog : Tendsto (fun n : Nat => Real.log ((U n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 (Real.log 2)))
    (hLtop : Tendsto (fun n => L n + 1) atTop atTop)
    (hUtop : Tendsto (fun n => U n + 1) atTop atTop)
    (hbounds : ∀ᶠ n : Nat in atTop,
      2 ≤ n ∧ 1 ≤ L n ∧ L n ≤ U n ∧ U n < sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop
      (𝓝 (criticalTopBandMass
        (criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))) c)) := by
  have hlow := sourceExpectedHighBandDensity_tendsto lam hlam c
    (fun n => L n + 1) hLlog hLtop
  have hupp := sourceExpectedHighBandDensity_tendsto lam hlam 0
    (fun n => U n + 1) (by simpa using hUlog) hUtop
  rw [criticalTopBandMass_zero] at hupp
  have hsub := hlow.sub hupp
  simpa only [sub_zero] using hsub.congr' (by
    filter_upwards [hbounds] with n hn
    rw [sourceTruncatedBandMean_eq_highNumerator_sub
      (calibrationExponent lam hlam n) n (L n) (U n)
      hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    dsimp only [sourceExpectedHighBandDensity]
    ring_nf)

/-- Source-faithful concentration inequality for the total degree in a
truncated band.  The variance cost is only `U / |X_n|` after normalizing the
deviation by the molecule count. -/
theorem sourceTruncatedBand_chebyshev_sq
    (a : ℝ) (n L U : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    {eps : ℝ} (heps : 0 < eps) :
    (∑ config : SourceMoleculeFibreConfig n,
      if eps ^ 2 ≤
          (∑ x : Molecule n,
            (truncatedBandValue L U (config x) -
              sourceTruncatedBandMean a n L U)) ^ 2 then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ((sourceMoleculeCount n : ℝ) * U * sourceTruncatedBandMean a n L U) /
        eps ^ 2 := by
  let p : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  let y : Finset (Reaction n) → ℝ := truncatedBandValue L U
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hp0 : ∀ A, 0 ≤ p A := by
    intro A
    exact subsetDegreeWeight_nonneg _
      (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hpow : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hpow.trans (sourceReactionCount_bounds hn).1
  have hp : ∑ A, p A = 1 := by
    dsimp [p]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hbound := finiteProduct_bounded_chebyshev_sq
    (I := Molecule n) p y hp0 hp
    (fun A => truncatedBandValue_nonneg L U A)
    (fun A => truncatedBandValue_le L U A) heps
  rw [card_binaryMolecule_eq_sourceMoleculeCount n] at hbound
  simpa [p, y, sourcePowerLawConfigWeight, sourceTruncatedBandMean] using hbound

/-- An `o(R_n)` degree cap converts the exact finite Chebyshev estimate into
convergence in probability after normalizing total retained degree by the
source reaction count. -/
theorem sourceTruncatedBand_deviation_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (L U : Nat → Nat) (q delta : ℝ)
    (hdelta : 0 < delta)
    (hUratio : Tendsto (fun n : Nat =>
      (U n : ℝ) / (sourceReactionCount n : ℝ)) atTop (𝓝 0))
    (hmean : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
        sourceTruncatedBandMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop (𝓝 q)) :
    Tendsto (fun n : Nat =>
      ∑ config : SourceMoleculeFibreConfig n,
        if (delta * (sourceReactionCount n : ℝ)) ^ 2 ≤
            (∑ x : Molecule n,
              (truncatedBandValue (L n) (U n) (config x) -
                sourceTruncatedBandMean (calibrationExponent lam hlam n)
                  n (L n) (U n))) ^ 2 then
          sourcePowerLawConfigWeight (calibrationExponent lam hlam n) n config
        else 0) atTop (𝓝 0) := by
  have haEv : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  have hupper : Tendsto (fun n : Nat =>
      ((U n : ℝ) / (sourceReactionCount n : ℝ)) *
        ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
          sourceTruncatedBandMean (calibrationExponent lam hlam n)
            n (L n) (U n)) / delta ^ 2) atTop (𝓝 0) := by
    have hmul := hUratio.mul hmean
    have hdiv := hmul.div_const (delta ^ 2)
    simpa only [zero_mul, zero_div] using hdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    hupper
  · filter_upwards [haEv] with n ha
    apply Finset.sum_nonneg
    intro config hconfig
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 4, haEv] with n hn ha
    have hRpos : (0 : ℝ) < sourceReactionCount n := by
      exact_mod_cast (show 0 < sourceReactionCount n by
        simp [sourceReactionCount])
    have heps : 0 < delta * (sourceReactionCount n : ℝ) :=
      mul_pos hdelta hRpos
    have hcheb := sourceTruncatedBand_chebyshev_sq
      (calibrationExponent lam hlam n) n (L n) (U n) ha hn heps
    calc
      (∑ config : SourceMoleculeFibreConfig n,
        if (delta * (sourceReactionCount n : ℝ)) ^ 2 ≤
            (∑ x : Molecule n,
              (truncatedBandValue (L n) (U n) (config x) -
                sourceTruncatedBandMean (calibrationExponent lam hlam n)
                  n (L n) (U n))) ^ 2 then
          sourcePowerLawConfigWeight (calibrationExponent lam hlam n) n config
        else 0) ≤
          ((sourceMoleculeCount n : ℝ) * U n *
            sourceTruncatedBandMean (calibrationExponent lam hlam n)
              n (L n) (U n)) /
                (delta * (sourceReactionCount n : ℝ)) ^ 2 := hcheb
      _ = ((U n : ℝ) / (sourceReactionCount n : ℝ)) *
          ((sourceMoleculeCount n : ℝ) / (sourceReactionCount n : ℝ) *
            sourceTruncatedBandMean (calibrationExponent lam hlam n)
              n (L n) (U n)) / delta ^ 2 := by
            field_simp [ne_of_gt hRpos, ne_of_gt hdelta]

/-- Indicator that a molecule's catalysis degree lies in `[L,U)`. -/
def truncatedBandIndicator {J : Type*} (L U : Nat) (A : Finset J) : ℝ :=
  if L ≤ A.card ∧ A.card < U then 1 else 0

theorem truncatedBandIndicator_nonneg {J : Type*}
    (L U : Nat) (A : Finset J) :
    0 ≤ truncatedBandIndicator L U A := by
  simp only [truncatedBandIndicator]
  split_ifs <;> norm_num

theorem truncatedBandIndicator_le_one {J : Type*}
    (L U : Nat) (A : Finset J) :
    truncatedBandIndicator L U A ≤ 1 := by
  simp only [truncatedBandIndicator]
  split_ifs <;> norm_num

noncomputable def sourceTruncatedBandCountMean
    (a : ℝ) (n L U : Nat) : ℝ :=
  ∑ A : Finset (Reaction n),
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A *
      truncatedBandIndicator L U A

theorem sourceTruncatedBandCountMean_eq_Ico
    (a : ℝ) (n L U : Nat) (hn : 2 ≤ n)
    (hU : U ≤ sourceReactionCount n + 1) :
    sourceTruncatedBandCountMean a n L U =
      ∑ d ∈ Finset.Ico L U,
        cappedZipfDegreeMass a (sourceReactionCount n) d := by
  have h := sum_subsetDegreeWeight_mul_cardFunction_eq
    (J := Reaction n) (cappedZipfDegreeMass a (sourceReactionCount n))
    (fun d => if L ≤ d ∧ d < U then (1 : ℝ) else 0)
  rw [card_binaryReaction_eq_sourceReactionCount hn] at h
  rw [show sourceTruncatedBandCountMean a n L U =
      ∑ A : Finset (Reaction n),
        subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A *
          (if L ≤ A.card ∧ A.card < U then (1 : ℝ) else 0) by
      simp only [sourceTruncatedBandCountMean, truncatedBandIndicator]]
  rw [h]
  calc
    (∑ d ∈ Finset.range (sourceReactionCount n + 1),
        cappedZipfDegreeMass a (sourceReactionCount n) d *
          (if L ≤ d ∧ d < U then (1 : ℝ) else 0)) =
        ∑ d ∈ Finset.range (sourceReactionCount n + 1),
          if L ≤ d ∧ d < U then
            cappedZipfDegreeMass a (sourceReactionCount n) d else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hp : L ≤ d ∧ d < U <;> simp [hp]
    _ = ∑ d ∈ (Finset.range (sourceReactionCount n + 1)).filter
          (fun d => L ≤ d ∧ d < U),
          cappedZipfDegreeMass a (sourceReactionCount n) d := by
            rw [Finset.sum_filter]
    _ = ∑ d ∈ Finset.Ico L U,
          cappedZipfDegreeMass a (sourceReactionCount n) d := by
            congr 1
            ext d
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
            omega

theorem rpowTail_sub_eq_sum_Ico
    {a : ℝ} (ha : 1 < a) {L U : Nat} (hLU : L ≤ U) :
    rpowTail a L - rpowTail a U =
      ∑ k ∈ Finset.Ico L U, (k : ℝ) ^ (-a) := by
  induction U, hLU using Nat.le_induction with
  | base => simp
  | succ U hLU ih =>
      rw [Finset.sum_Ico_succ_top hLU, ← ih]
      rw [rpowTail_eq_head_add ha U]
      ring

theorem cappedZipfDegreeMass_Ico_eq_tailDifference
    (a : ℝ) (R L U : Nat) (ha : 1 < a)
    (hLU : L ≤ U) (hUR : U < R) :
    (∑ d ∈ Finset.Ico L U, cappedZipfDegreeMass a R d) =
      zipfTailRatio a (L + 1) - zipfTailRatio a (U + 1) := by
  rw [zipfTailRatio, zipfTailRatio, ← sub_div]
  rw [rpowTail_sub_eq_sum_Ico ha (show L + 1 ≤ U + 1 by omega)]
  rw [Finset.sum_div]
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  rw [show U + 1 - (L + 1) = U - L by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi : i < U - L := Finset.mem_range.mp hi
  have hdegree : L + i + 1 < R := by omega
  rw [cappedZipfDegreeMass, if_pos hdegree]
  push_cast
  ring_nf

theorem sourceTruncatedBandCountMean_eq_tailDifference
    (a : ℝ) (n L U : Nat) (ha : 1 < a) (hn : 2 ≤ n)
    (hLU : L ≤ U) (hUR : U < sourceReactionCount n) :
    sourceTruncatedBandCountMean a n L U =
      zipfTailRatio a (L + 1) - zipfTailRatio a (U + 1) := by
  rw [sourceTruncatedBandCountMean_eq_Ico a n L U hn (by omega)]
  exact cappedZipfDegreeMass_Ico_eq_tailDifference a
    (sourceReactionCount n) L U ha hLU hUR

/-- A strict gap between normalized logarithmic growth rates forces the ratio
of the corresponding positive integer sequences to vanish. -/
theorem natRatio_tendsto_zero_of_log_normalized_lt
    (m u : Nat → Nat) (alpha beta : ℝ) (hab : alpha < beta)
    (hmlog : Tendsto (fun n : Nat => Real.log (m n : ℝ) / (n : ℝ))
      atTop (𝓝 alpha))
    (hulog : Tendsto (fun n : Nat => Real.log (u n : ℝ) / (n : ℝ))
      atTop (𝓝 beta))
    (hmtop : Tendsto m atTop atTop) (hutop : Tendsto u atTop atTop) :
    Tendsto (fun n : Nat => (m n : ℝ) / (u n : ℝ)) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n : Nat =>
      Real.log (u n : ℝ) / (n : ℝ) -
        Real.log (m n : ℝ) / (n : ℝ)) atTop (𝓝 (beta - alpha)) :=
    hulog.sub hmlog
  have hgap : 0 < beta - alpha := sub_pos.mpr hab
  have hscale : Tendsto (fun n : Nat =>
      (n : ℝ) * (Real.log (u n : ℝ) / (n : ℝ) -
        Real.log (m n : ℝ) / (n : ℝ))) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_pos hgap hdiff
  have hneg : Tendsto (fun n : Nat =>
      -((n : ℝ) * (Real.log (u n : ℝ) / (n : ℝ) -
        Real.log (m n : ℝ) / (n : ℝ)))) atTop atBot := by
    rw [tendsto_atBot]
    intro B
    filter_upwards [hscale.eventually_ge_atTop (-B)] with n hn
    linarith
  have hexp := Real.tendsto_exp_atBot.comp hneg
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1,
    hmtop.eventually (eventually_gt_atTop 0),
    hutop.eventually (eventually_gt_atTop 0)] with n hn hm hu
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hexponent :
      -((n : ℝ) * (Real.log (u n : ℝ) / (n : ℝ) -
        Real.log (m n : ℝ) / (n : ℝ))) =
        Real.log (m n : ℝ) - Real.log (u n : ℝ) := by
    field_simp [hn0]
    ring
  simp only [Function.comp_apply]
  rw [hexponent, Real.exp_sub,
    Real.exp_log (by exact_mod_cast hm),
    Real.exp_log (by exact_mod_cast hu)]

/-- At a positive band exponent, the truncated per-molecule band probability
is asymptotic to a positive constant divided by its lower mark threshold. -/
theorem sourceTruncatedBandCountMean_scaled_tendsto
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (hc : 0 < c)
    (L U : Nat → Nat)
    (hLlog : Tendsto (fun n : Nat => Real.log ((L n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 ((1 - c) * Real.log 2)))
    (hUlog : Tendsto (fun n : Nat => Real.log ((U n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 (Real.log 2)))
    (hLtop : Tendsto (fun n => L n + 1) atTop atTop)
    (hUtop : Tendsto (fun n => U n + 1) atTop atTop)
    (hbounds : ∀ᶠ n : Nat in atTop,
      2 ≤ n ∧ L n ≤ U n ∧ U n < sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      ((L n + 1 : Nat) : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop
      (𝓝 (Real.exp
        (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) *
          ((1 - c) * Real.log 2)) / (Real.pi ^ 2 / 6))) := by
  let b := criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ))
  have hb : Tendsto (fun n : Nat =>
      (n : ℝ) * (calibrationExponent lam hlam n - 2)) atTop (𝓝 b) := by
    apply (calibrationB_tendsto_inverse lam hlam).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [calibrationExponent]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
    ring
  have hlow := movingZipfTail (calibrationExponent lam hlam)
    (fun n => L n + 1) b ((1 - c) * Real.log 2)
    (calibrationExponent_tendsto_two lam hlam) hb hLlog hLtop
  have hupp := movingZipfTail (calibrationExponent lam hlam)
    (fun n => U n + 1) b (Real.log 2)
    (calibrationExponent_tendsto_two lam hlam) hb hUlog hUtop
  have hrate : (1 - c) * Real.log 2 < Real.log 2 := by
    nlinarith [Real.log_pos one_lt_two]
  have hratio := natRatio_tendsto_zero_of_log_normalized_lt
    (fun n => L n + 1) (fun n => U n + 1)
    ((1 - c) * Real.log 2) (Real.log 2) hrate
    hLlog hUlog hLtop hUtop
  have huppScaled := hratio.mul hupp
  have hsub := hlow.sub huppScaled
  have haEv : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  simpa only [zero_mul, sub_zero, b] using hsub.congr' (by
    filter_upwards [hbounds, haEv,
      hUtop.eventually (eventually_gt_atTop 0)] with n hn ha hupos
    rw [sourceTruncatedBandCountMean_eq_tailDifference
      (calibrationExponent lam hlam n) n (L n) (U n)
      ha hn.1 hn.2.1 hn.2.2]
    have hu0 : ((U n + 1 : Nat) : ℝ) ≠ 0 := by exact_mod_cast hupos.ne'
    field_simp [hu0])

theorem sourceTruncatedBandExpectedCount_tendsto_atTop
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (hc : 0 < c)
    (L U : Nat → Nat)
    (hLlog : Tendsto (fun n : Nat => Real.log ((L n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 ((1 - c) * Real.log 2)))
    (hUlog : Tendsto (fun n : Nat => Real.log ((U n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 (Real.log 2)))
    (hLtop : Tendsto (fun n => L n + 1) atTop atTop)
    (hUtop : Tendsto (fun n => U n + 1) atTop atTop)
    (hbounds : ∀ᶠ n : Nat in atTop,
      2 ≤ n ∧ L n ≤ U n ∧ U n < sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop atTop := by
  let C : ℝ := Real.exp
    (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) *
      ((1 - c) * Real.log 2)) / (Real.pi ^ 2 / 6)
  have hscaled := sourceTruncatedBandCountMean_scaled_tendsto
    lam hlam c hc L U hLlog hUlog hLtop hUtop hbounds
  have hscaledC : Tendsto (fun n : Nat =>
      ((L n + 1 : Nat) : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop (𝓝 C) := by
    simpa only [C] using hscaled
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hrate : (1 - c) * Real.log 2 < Real.log 2 := by
    nlinarith [Real.log_pos one_lt_two]
  have hratio := natRatio_tendsto_zero_of_log_normalized_lt
    (fun n => L n + 1) sourceMoleculeCount
    ((1 - c) * Real.log 2) (Real.log 2) hrate
    hLlog log_sourceMoleculeCount_normalized hLtop
    sourceMoleculeCount_tendsto_atTop
  have hratioPos : ∀ᶠ n : Nat in atTop,
      0 < ((L n + 1 : Nat) : ℝ) / (sourceMoleculeCount n : ℝ) := by
    filter_upwards [hLtop.eventually (eventually_gt_atTop 0),
      sourceMoleculeCount_tendsto_atTop.eventually
        (eventually_gt_atTop 0)] with n hL hX
    positivity
  have hratioWithin : Tendsto (fun n : Nat =>
      ((L n + 1 : Nat) : ℝ) / (sourceMoleculeCount n : ℝ))
      atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hratio, hratioPos⟩
  have hinv := hratioWithin.inv_tendsto_nhdsGT_zero
  have hproduct := hinv.atTop_mul_pos hC hscaledC
  apply hproduct.congr'
  filter_upwards [hLtop.eventually (eventually_gt_atTop 0),
    sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hL hX
  have hL0 : ((L n + 1 : Nat) : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hX0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  simp only [Pi.inv_apply]
  field_simp [hL0, hX0]

theorem sourceTruncatedBandExpectedCount_log_normalized
    (lam : ℝ) (hlam : 0 < lam) (c : ℝ) (hc : 0 < c)
    (L U : Nat → Nat)
    (hLlog : Tendsto (fun n : Nat => Real.log ((L n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 ((1 - c) * Real.log 2)))
    (hUlog : Tendsto (fun n : Nat => Real.log ((U n + 1 : Nat) : ℝ) /
      (n : ℝ)) atTop (𝓝 (Real.log 2)))
    (hLtop : Tendsto (fun n => L n + 1) atTop atTop)
    (hUtop : Tendsto (fun n => U n + 1) atTop atTop)
    (hbounds : ∀ᶠ n : Nat in atTop,
      2 ≤ n ∧ L n ≤ U n ∧ U n < sourceReactionCount n) :
    Tendsto (fun n : Nat =>
      Real.log ((sourceMoleculeCount n : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n)) / (n : ℝ)) atTop (𝓝 (c * Real.log 2)) := by
  let C : ℝ := Real.exp
    (-criticalLambdaInv (⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) *
      ((1 - c) * Real.log 2)) / (Real.pi ^ 2 / 6)
  let S : Nat → ℝ := fun n => ((L n + 1 : Nat) : ℝ) *
    sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
      n (L n) (U n)
  have hS : Tendsto S atTop (𝓝 C) := by
    simpa only [S, C] using sourceTruncatedBandCountMean_scaled_tendsto
      lam hlam c hc L U hLlog hUlog hLtop hUtop hbounds
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlogS : Tendsto (fun n => Real.log (S n)) atTop (𝓝 (Real.log C)) :=
    (Real.continuousAt_log hC.ne').tendsto.comp hS
  have hlogSdiv : Tendsto (fun n => Real.log (S n) / (n : ℝ))
      atTop (𝓝 0) := hlogS.div_atTop
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlimit :=
    (log_sourceMoleculeCount_normalized.sub hLlog).add hlogSdiv
  have hlimit' : Tendsto (fun n : Nat =>
      Real.log (sourceMoleculeCount n : ℝ) / (n : ℝ) -
        Real.log ((L n + 1 : Nat) : ℝ) / (n : ℝ) +
          Real.log (S n) / (n : ℝ)) atTop (𝓝 (c * Real.log 2)) := by
    (convert hlimit using 1; ring)
  apply hlimit'.congr'
  filter_upwards [eventually_ge_atTop 1,
    hS.eventually (Ioi_mem_nhds hC),
    hLtop.eventually (eventually_gt_atTop 0),
    sourceMoleculeCount_tendsto_atTop.eventually
      (eventually_gt_atTop 0)] with n hn hSn hLn hXn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hL0 : ((L n + 1 : Nat) : ℝ) ≠ 0 := by exact_mod_cast hLn.ne'
  have hX0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast hXn.ne'
  have hmean : 0 < sourceTruncatedBandCountMean
      (calibrationExponent lam hlam n) n (L n) (U n) := by
    have : 0 < ((L n + 1 : Nat) : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n) := by simpa only [S] using hSn
    rcases mul_pos_iff.mp this with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge (by positivity)) hneg.1)
  rw [Real.log_mul hX0 (ne_of_gt hmean),
    show S n = ((L n + 1 : Nat) : ℝ) *
      sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
        n (L n) (U n) by rfl,
    Real.log_mul hL0 (ne_of_gt hmean)]
  field_simp [hn0]
  ring

/-- Exact finite concentration inequality for the number of molecules whose
degrees lie in the selected band. -/
theorem sourceTruncatedBandCount_chebyshev_sq
    (a : ℝ) (n L U : Nat) (ha : 1 < a) (hn : 4 ≤ n)
    {eps : ℝ} (heps : 0 < eps) :
    (∑ config : SourceMoleculeFibreConfig n,
      if eps ^ 2 ≤
          (∑ x : Molecule n,
            (truncatedBandIndicator L U (config x) -
              sourceTruncatedBandCountMean a n L U)) ^ 2 then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ((sourceMoleculeCount n : ℝ) *
        sourceTruncatedBandCountMean a n L U) / eps ^ 2 := by
  let p : Finset (Reaction n) → ℝ := fun A =>
    subsetDegreeWeight (cappedZipfDegreeMass a (sourceReactionCount n)) A
  let y : Finset (Reaction n) → ℝ := truncatedBandIndicator L U
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hp0 : ∀ A, 0 ≤ p A := by
    intro A
    exact subsetDegreeWeight_nonneg _
      (fun d => cappedZipfDegreeMass_nonneg a _ d hzpos) A
  have hcard := card_binaryReaction_eq_sourceReactionCount (n := n) (by omega)
  have hR : 2 ≤ sourceReactionCount n := by
    have hpow : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact hpow.trans (sourceReactionCount_bounds hn).1
  have hp : ∑ A, p A = 1 := by
    dsimp [p]
    rw [← hcard]
    exact sum_powerLawSubsetWeight_eq_one a ha (hcard.symm ▸ hR)
  have hbound := finiteProduct_bounded_chebyshev_sq
    (I := Molecule n) p y hp0 hp
    (fun A => truncatedBandIndicator_nonneg L U A)
    (fun A => truncatedBandIndicator_le_one L U A) heps
  rw [card_binaryMolecule_eq_sourceMoleculeCount n] at hbound
  simpa [p, y, sourcePowerLawConfigWeight,
    sourceTruncatedBandCountMean] using hbound

/-- Once the expected number of selected molecules diverges, the selected
count is relatively concentrated around that expectation. -/
theorem sourceTruncatedBandCount_relative_deviation_tendsto_zero
    (lam : ℝ) (hlam : 0 < lam) (L U : Nat → Nat) (delta : ℝ)
    (hdelta : 0 < delta)
    (hExpected : Tendsto (fun n : Nat =>
      (sourceMoleculeCount n : ℝ) *
        sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
          n (L n) (U n)) atTop atTop) :
    Tendsto (fun n : Nat =>
      ∑ config : SourceMoleculeFibreConfig n,
        if (delta * ((sourceMoleculeCount n : ℝ) *
            sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
              n (L n) (U n))) ^ 2 ≤
            (∑ x : Molecule n,
              (truncatedBandIndicator (L n) (U n) (config x) -
                sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
                  n (L n) (U n))) ^ 2 then
          sourcePowerLawConfigWeight (calibrationExponent lam hlam n) n config
        else 0) atTop (𝓝 0) := by
  let E : Nat → ℝ := fun n =>
    (sourceMoleculeCount n : ℝ) *
      sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
        n (L n) (U n)
  have hE : Tendsto E atTop atTop := by simpa only [E] using hExpected
  have hEinv : Tendsto (fun n => (E n)⁻¹) atTop (𝓝 0) :=
    hE.inv_tendsto_atTop
  have hupper : Tendsto (fun n => 1 / (delta ^ 2 * E n))
      atTop (𝓝 0) := by
    have hmul := hEinv.const_mul ((delta ^ 2)⁻¹)
    have hmul' : Tendsto (fun n => (delta ^ 2)⁻¹ * (E n)⁻¹)
        atTop (𝓝 0) := by simpa only [mul_zero] using hmul
    apply hmul'.congr'
    filter_upwards [hE.eventually (eventually_gt_atTop 0)] with n hEn
    field_simp [ne_of_gt hdelta, ne_of_gt hEn]
  have haEv : ∀ᶠ n : Nat in atTop,
      1 < calibrationExponent lam hlam n :=
    (calibrationExponent_tendsto_two lam hlam) (Ioi_mem_nhds one_lt_two)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    hupper
  · filter_upwards [haEv] with n ha
    apply Finset.sum_nonneg
    intro config hconfig
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [eventually_ge_atTop 4, haEv,
      hE.eventually (eventually_gt_atTop 0)] with n hn ha hEn
    have heps : 0 < delta * E n := mul_pos hdelta hEn
    have hcheb := sourceTruncatedBandCount_chebyshev_sq
      (calibrationExponent lam hlam n) n (L n) (U n) ha hn heps
    calc
      (∑ config : SourceMoleculeFibreConfig n,
        if (delta * E n) ^ 2 ≤
            (∑ x : Molecule n,
              (truncatedBandIndicator (L n) (U n) (config x) -
                sourceTruncatedBandCountMean (calibrationExponent lam hlam n)
                  n (L n) (U n))) ^ 2 then
          sourcePowerLawConfigWeight (calibrationExponent lam hlam n) n config
        else 0) ≤ E n / (delta * E n) ^ 2 := hcheb
      _ = 1 / (delta ^ 2 * E n) := by
        field_simp [ne_of_gt hdelta, ne_of_gt hEn]

end PowerLawSmallRAF

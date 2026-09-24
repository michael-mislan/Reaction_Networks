import proofs.PowerLawSmallRAF.SourceLowDegreeScale

namespace PowerLawSmallRAF

/-- Outcomes certified by one code: the target is fixed by the code, while
the environmental coordinate ranges over the compatible fibres. -/
def certificateFibre {Target Environment Code : Type*}
    [Fintype Environment] [DecidableEq Target] [DecidableEq Environment]
    (output : Code → Target) (compatible : Code → Environment → Prop)
    [∀ c, DecidablePred (compatible c)] (c : Code) :
    Finset (Target × Environment) :=
  (Finset.univ.filter (compatible c)).image (fun ω => (output c, ω))

/-- Union of all target-environment outcomes having at least one certificate. -/
def certificateUnion {Target Environment Code : Type*}
    [Fintype Code] [Fintype Environment]
    [DecidableEq Target] [DecidableEq Environment]
    (output : Code → Target) (compatible : Code → Environment → Prop)
    [∀ c, DecidablePred (compatible c)] : Finset (Target × Environment) :=
  Finset.univ.biUnion (certificateFibre output compatible)

/-- Exact finite union bound: overlap between certificates can only reduce the
number of successful target-environment outcomes. -/
theorem card_certificateUnion_le_sum_compatible
    {Target Environment Code : Type*}
    [Fintype Code] [Fintype Environment]
    [DecidableEq Target] [DecidableEq Environment]
    (output : Code → Target) (compatible : Code → Environment → Prop)
    [∀ c, DecidablePred (compatible c)] :
    (certificateUnion output compatible).card ≤
      ∑ c : Code, (Finset.univ.filter (compatible c)).card := by
  dsimp [certificateUnion]
  refine Finset.card_biUnion_le.trans ?_
  apply Finset.sum_le_sum
  intro c hc
  dsimp [certificateFibre]
  exact Finset.card_image_le

/-- Real-valued uniform-mass form of the certificate union bound. -/
theorem certificateUnion_uniformMass_le
    {Target Environment Code : Type*}
    [Fintype Target] [Fintype Code] [Fintype Environment]
    [DecidableEq Target] [DecidableEq Environment]
    (output : Code → Target) (compatible : Code → Environment → Prop)
    [∀ c, DecidablePred (compatible c)] :
    ((certificateUnion output compatible).card : ℝ) /
        (Fintype.card Target * Fintype.card Environment) ≤
      (∑ c : Code, ((Finset.univ.filter (compatible c)).card : ℝ)) /
        (Fintype.card Target * Fintype.card Environment) := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast card_certificateUnion_le_sum_compatible output compatible
  · positivity

/-- If every certificate is compatible with at most a `p` fraction of the
environmental fibres, then the joint uniform event costs at most the number
of codes divided by the number of targets, times `p`. -/
theorem certificateUnion_uniformMass_le_codeRatio_mul
    {Target Environment Code : Type*}
    [Fintype Target] [Fintype Code] [Fintype Environment]
    [DecidableEq Target] [DecidableEq Environment]
    (output : Code → Target) (compatible : Code → Environment → Prop)
    [∀ c, DecidablePred (compatible c)] (p : ℝ)
    (hTarget : 0 < Fintype.card Target)
    (hEnvironment : 0 < Fintype.card Environment)
    (hcompatible : ∀ c : Code,
      ((Finset.univ.filter (compatible c)).card : ℝ) /
          Fintype.card Environment ≤ p) :
    ((certificateUnion output compatible).card : ℝ) /
        (Fintype.card Target * Fintype.card Environment) ≤
      (Fintype.card Code : ℝ) / Fintype.card Target * p := by
  have hT0 : (Fintype.card Target : ℝ) ≠ 0 := by positivity
  have hE0 : (Fintype.card Environment : ℝ) ≠ 0 := by positivity
  calc
    ((certificateUnion output compatible).card : ℝ) /
        (Fintype.card Target * Fintype.card Environment) ≤
      (∑ c : Code, ((Finset.univ.filter (compatible c)).card : ℝ)) /
        (Fintype.card Target * Fintype.card Environment) :=
      certificateUnion_uniformMass_le output compatible
    _ = (1 / Fintype.card Target) *
        ((∑ c : Code, ((Finset.univ.filter (compatible c)).card : ℝ)) /
          Fintype.card Environment) := by
      field_simp
    _ = (1 / Fintype.card Target) *
        ∑ c : Code,
          ((Finset.univ.filter (compatible c)).card : ℝ) /
            Fintype.card Environment := by rw [Finset.sum_div]
    _ ≤ (1 / Fintype.card Target) * ∑ _c : Code, p := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun c _ => hcompatible c
      · positivity
    _ = (Fintype.card Code : ℝ) / Fintype.card Target * p := by
      simp
      ring

end PowerLawSmallRAF

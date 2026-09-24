import proofs.PowerLawSmallRAF.FixedSizeFibreCertificates

namespace PowerLawSmallRAF

/-- One exact instruction-count layer of gateway-conditioned legal ligation
certificates.  The output and required-channel maps may encode any concrete
source realization; only the chronological code count and the `s-1` distinct
nongateway channels enter the bound. -/
theorem legalLigationCertificateLayer_uniformMass_le
    (foodCount targetCount reactionCount degree instructionCount : Nat)
    (output : LegalLigationProgramCode foodCount instructionCount → Fin targetCount)
    (required : LegalLigationProgramCode foodCount instructionCount →
      Finset (Fin (reactionCount - 1)))
    (hrequired : ∀ code, (required code).card = instructionCount - 1)
    (htarget : 0 < targetCount) (hdegree : 1 ≤ degree)
    (hdegreeR : degree ≤ reactionCount)
    (hinstructions : instructionCount ≤ degree) :
    ((certificateUnion output
      (fun (code : LegalLigationProgramCode foodCount instructionCount)
        (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
          fixedSizeFibreContains (required code) fibre)).card : ℝ) /
        (targetCount *
          Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1))) ≤
      (((foodCount + instructionCount) ^ (2 * instructionCount) : Nat) : ℝ) /
        targetCount *
          gatewayConditionedContain reactionCount (instructionCount - 1) degree := by
  have hq : instructionCount - 1 ≤ degree - 1 := by omega
  have hdR' : degree - 1 ≤ reactionCount - 1 := by omega
  have hlayer := fixedSizeCertificateUnion_uniformMass_le
    output required hrequired hq hdR' (by simpa using htarget)
  have hlayer' :
      ((certificateUnion output
        (fun (code : LegalLigationProgramCode foodCount instructionCount)
          (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
            fixedSizeFibreContains (required code) fibre)).card : ℝ) /
          (targetCount *
            Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1))) ≤
        (Fintype.card
          (LegalLigationProgramCode foodCount instructionCount) : ℝ) /
            targetCount *
          gatewayConditionedContain reactionCount (instructionCount - 1) degree := by
    simpa only [Fintype.card_fin, gatewayConditionedContain] using hlayer
  have hp : 0 ≤ gatewayConditionedContain reactionCount
      (instructionCount - 1) degree := by
    rw [gatewayConditionedContain_eq_symmetricChoose reactionCount
      (instructionCount - 1) degree hdegree hdegreeR hq]
    exact div_nonneg (by positivity) (by positivity)
  refine hlayer'.trans ?_
  apply mul_le_mul_of_nonneg_right
  · apply div_le_div_of_nonneg_right
    · exact_mod_cast card_legalLigationProgramCode_le foodCount instructionCount
    · positivity
  · exact hp

/-- Union of all legal certificate layers up to `instructionCap`. -/
def legalLigationCertificateEvent
    (foodCount targetCount reactionCount degree instructionCap : Nat)
    (output : ∀ s, LegalLigationProgramCode foodCount s → Fin targetCount)
    (required : ∀ s, LegalLigationProgramCode foodCount s →
      Finset (Fin (reactionCount - 1))) :
    Finset (Fin targetCount ×
      FixedSizeFibre (reactionCount - 1) (degree - 1)) :=
  (Finset.Icc 1 instructionCap).biUnion fun s =>
    certificateUnion (output s)
      (fun (code : LegalLigationProgramCode foodCount s)
        (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
          fixedSizeFibreContains (required s code) fibre)

/-- The exact multi-length certificate event is bounded by the previously
defined grammar envelope. -/
theorem legalLigationCertificateEvent_uniformMass_le_envelope
    (foodCount targetCount reactionCount degree instructionCap : Nat)
    (output : ∀ s, LegalLigationProgramCode foodCount s → Fin targetCount)
    (required : ∀ s, LegalLigationProgramCode foodCount s →
      Finset (Fin (reactionCount - 1)))
    (hrequired : ∀ s ∈ Finset.Icc 1 instructionCap,
      ∀ code, (required s code).card = s - 1)
    (htarget : 0 < targetCount) (hdegree : 1 ≤ degree)
    (hdegreeR : degree ≤ reactionCount) (hcap : instructionCap ≤ degree) :
    ((legalLigationCertificateEvent foodCount targetCount reactionCount degree
      instructionCap output required).card : ℝ) /
        (targetCount *
          Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1))) ≤
      gatewayGrammarEnvelope foodCount targetCount reactionCount degree
        instructionCap := by
  let denominator : ℝ := targetCount *
    Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1))
  have hden : 0 ≤ denominator := by positivity
  have hcard :
      (legalLigationCertificateEvent foodCount targetCount reactionCount degree
        instructionCap output required).card ≤
        ∑ s ∈ Finset.Icc 1 instructionCap,
          (certificateUnion (output s)
            (fun (code : LegalLigationProgramCode foodCount s)
              (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
              fixedSizeFibreContains (required s code) fibre)).card := by
    exact Finset.card_biUnion_le
  calc
    ((legalLigationCertificateEvent foodCount targetCount reactionCount degree
      instructionCap output required).card : ℝ) / denominator ≤
        ((∑ s ∈ Finset.Icc 1 instructionCap,
          (certificateUnion (output s)
            (fun (code : LegalLigationProgramCode foodCount s)
              (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
              fixedSizeFibreContains (required s code) fibre)).card : Nat) : ℝ) /
          denominator := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · exact hden
    _ = ∑ s ∈ Finset.Icc 1 instructionCap,
        ((certificateUnion (output s)
          (fun (code : LegalLigationProgramCode foodCount s)
            (fibre : FixedSizeFibre (reactionCount - 1) (degree - 1)) =>
            fixedSizeFibreContains (required s code) fibre)).card : ℝ) /
          denominator := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ s ∈ Finset.Icc 1 instructionCap,
        (((foodCount + s) ^ (2 * s) : Nat) : ℝ) / targetCount *
          gatewayConditionedContain reactionCount (s - 1) degree := by
      apply Finset.sum_le_sum
      intro s hs
      exact legalLigationCertificateLayer_uniformMass_le
        foodCount targetCount reactionCount degree s (output s) (required s)
        (hrequired s hs) htarget hdegree hdegreeR
        ((Finset.mem_Icc.mp hs).2.trans hcap)
    _ = gatewayGrammarEnvelope foodCount targetCount reactionCount degree
        instructionCap := by rfl

end PowerLawSmallRAF

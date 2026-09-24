import proofs.PowerLawSmallRAF.ReversibleReachabilityBridge
import proofs.PowerLawSmallRAF.FixedSizeFibreCertificates

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

def binaryFoodEmbedMoleculeTwo {n : Nat}
    (x : {x : Molecule n // x ∈ binaryFood n 2}) : Molecule 2 :=
  ⟨⟨x.val.1.val, by
      have hx := (Finset.mem_filter.mp x.property).2
      dsimp [molLength] at hx
      omega⟩,
    x.val.2⟩

theorem binaryFoodEmbedMoleculeTwo_injective {n : Nat} :
    Function.Injective (@binaryFoodEmbedMoleculeTwo n) := by
  rintro ⟨⟨ai, aw⟩, ha⟩ ⟨⟨bi, bw⟩, hb⟩ h
  apply Subtype.ext
  have hi : ai = bi := by
    apply Fin.ext
    exact congrArg (fun z : Molecule 2 => z.1.val) h
  subst bi
  congr
  apply Fin.ext
  exact congrArg (fun z : Molecule 2 => z.2.val) h

theorem card_binaryFood_two_le_six (n : Nat) :
    (binaryFood n 2).card ≤ 6 := by
  calc
    (binaryFood n 2).card = Fintype.card {x // x ∈ binaryFood n 2} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Molecule 2) :=
      Fintype.card_le_of_injective binaryFoodEmbedMoleculeTwo
        binaryFoodEmbedMoleculeTwo_injective
    _ = 6 := card_food_binary_t2

/-- The actual finite family of legal distinct enabled source traces. -/
abbrev ReversibleTraceCode (n s : Nat) :=
  {trace : List (Reaction n) //
    trace ∈ reversibleTraceFinset (binaryFood n 2) s}

@[simp] theorem card_reversibleTraceCode (n s : Nat) :
    Fintype.card (ReversibleTraceCode n s) =
      (reversibleTraceFinset (binaryFood n 2) s).card := by
  exact Fintype.card_coe _

theorem card_reversibleTraceCode_le (n s : Nat) (hsn : s ≤ n) :
    Fintype.card (ReversibleTraceCode n s) ≤
      sourceReversibleBranchCount n ^ s := by
  rw [card_reversibleTraceCode]
  exact card_reversibleTraceFinset_le_pow (by
    exact card_binaryFood_two_le_six n) hsn

/-- A cleavage step can first expose two possible marked molecules, so a
first-hit certificate carries one extra binary output selector. -/
abbrev ReversibleFirstHitCode (n s : Nat) :=
  ReversibleTraceCode n s × Fin 2

theorem card_reversibleFirstHitCode_le (n s : Nat) (hsn : s ≤ n) :
    Fintype.card (ReversibleFirstHitCode n s) ≤
      2 * sourceReversibleBranchCount n ^ s := by
  simp only [ReversibleFirstHitCode, Fintype.card_prod, Fintype.card_fin]
  simpa [Nat.mul_comm] using
    Nat.mul_le_mul_left 2 (card_reversibleTraceCode_le n s hsn)

/-- One fixed-length first-hit trace layer under gateway conditioning. -/
def reversibleFirstHitCertificateLayer
    (n targetCount reactionCount degree s : Nat)
    (output : ReversibleFirstHitCode n s → Fin targetCount)
    (required : ReversibleFirstHitCode n s →
      Finset (Fin (reactionCount - 1))) :
    Finset (Fin targetCount ×
      FixedSizeFibre (reactionCount - 1) (degree - 1)) :=
  certificateUnion output fun code fibre =>
    fixedSizeFibreContains (required code) fibre

theorem reversibleFirstHitCertificateLayer_uniformMass_le
    (n targetCount reactionCount degree s : Nat)
    (output : ReversibleFirstHitCode n s → Fin targetCount)
    (required : ReversibleFirstHitCode n s →
      Finset (Fin (reactionCount - 1)))
    (hrequired : ∀ code, (required code).card = s - 1)
    (hs1 : 1 ≤ s) (hsn : s ≤ n) (hsd : s ≤ degree)
    (htarget : 0 < targetCount) (hdegree : 1 ≤ degree)
    (hdegreeR : degree ≤ reactionCount) :
    ((reversibleFirstHitCertificateLayer n targetCount reactionCount degree s
      output required).card : ℝ) /
        (targetCount * Fintype.card
          (FixedSizeFibre (reactionCount - 1) (degree - 1))) ≤
      (2 : ℝ) *
        (((sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
          gatewayConditionedContain reactionCount (s - 1) degree) := by
  have hq : s - 1 ≤ degree - 1 := by omega
  have hdR : degree - 1 ≤ reactionCount - 1 := by omega
  have hbase := fixedSizeCertificateUnion_uniformMass_le
    output required hrequired hq hdR (by simpa using htarget)
  have hcontain : 0 ≤ gatewayConditionedContain reactionCount (s - 1) degree :=
    div_nonneg (by positivity) (by positivity)
  calc
    ((reversibleFirstHitCertificateLayer n targetCount reactionCount degree s
      output required).card : ℝ) /
        (targetCount * Fintype.card
          (FixedSizeFibre (reactionCount - 1) (degree - 1))) ≤
      (Fintype.card (ReversibleFirstHitCode n s) : ℝ) / targetCount *
        gatewayConditionedContain reactionCount (s - 1) degree := by
      simpa only [reversibleFirstHitCertificateLayer, Fintype.card_fin,
        gatewayConditionedContain] using hbase
    _ ≤ ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
        gatewayConditionedContain reactionCount (s - 1) degree := by
      apply mul_le_mul_of_nonneg_right _ hcontain
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_reversibleFirstHitCode_le n s hsn
    _ = (2 : ℝ) *
        (((sourceReversibleBranchCount n ^ s : Nat) : ℝ) / targetCount *
          gatewayConditionedContain reactionCount (s - 1) degree) := by
      push_cast
      ring

/-- A length-`n` surviving trace is a certificate on the fibre alone. -/
def reversibleSurvivalCertificateEvent
    (n reactionCount degree : Nat)
    (required : ReversibleTraceCode n n →
      Finset (Fin (reactionCount - 1))) :
    Finset (FixedSizeFibre (reactionCount - 1) (degree - 1)) :=
  Finset.univ.biUnion fun code =>
    Finset.univ.filter fun fibre => fixedSizeFibreContains (required code) fibre

theorem reversibleSurvivalCertificateEvent_uniformMass_le
    (n reactionCount degree : Nat)
    (required : ReversibleTraceCode n n →
      Finset (Fin (reactionCount - 1)))
    (hrequired : ∀ code, (required code).card = n - 1)
    (hnDegree : n ≤ degree) (hdegree : 1 ≤ degree)
    (hdegreeR : degree ≤ reactionCount) :
    ((reversibleSurvivalCertificateEvent n reactionCount degree required).card : ℝ) /
        Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1)) ≤
      ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
        gatewayConditionedContain reactionCount (n - 1) degree := by
  have hq : n - 1 ≤ degree - 1 := by omega
  have hdR : degree - 1 ≤ reactionCount - 1 := by omega
  have hcard : (reversibleSurvivalCertificateEvent n reactionCount degree
      required).card ≤ ∑ code : ReversibleTraceCode n n,
        (Finset.univ.filter fun fibre :
          FixedSizeFibre (reactionCount - 1) (degree - 1) =>
            fixedSizeFibreContains (required code) fibre).card :=
    Finset.card_biUnion_le
  have hden : 0 ≤ (Fintype.card
      (FixedSizeFibre (reactionCount - 1) (degree - 1)) : ℝ) := by positivity
  calc
    ((reversibleSurvivalCertificateEvent n reactionCount degree required).card : ℝ) /
        Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1)) ≤
      ((∑ code : ReversibleTraceCode n n,
        (Finset.univ.filter fun fibre :
          FixedSizeFibre (reactionCount - 1) (degree - 1) =>
            fixedSizeFibreContains (required code) fibre).card : Nat) : ℝ) /
        Fintype.card (FixedSizeFibre (reactionCount - 1) (degree - 1)) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = ∑ _code : ReversibleTraceCode n n,
        hypergeometricContain (reactionCount - 1) (n - 1) (degree - 1) := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro code _
      exact fixedSizeFibre_containing_fraction
        (required code) (hrequired code) hq
    _ = (Fintype.card (ReversibleTraceCode n n) : ℝ) *
        gatewayConditionedContain reactionCount (n - 1) degree := by
      simp [gatewayConditionedContain]
    _ ≤ ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
        gatewayConditionedContain reactionCount (n - 1) degree := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_reversibleTraceCode_le n n (le_refl n)
      · exact div_nonneg (by positivity) (by positivity)

end PowerLawSmallRAF

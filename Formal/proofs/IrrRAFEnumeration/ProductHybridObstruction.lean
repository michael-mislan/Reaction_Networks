import proofs.IrrRAFEnumeration.ProductComposition

namespace IrrRAFEnumeration

/-- The three finite objects memoized by the hybrid dualization recursion. -/
structure HybridState (α : Type*) where
  ambient : Finset α
  positive : Finset (Finset α)
  negative : Finset (Finset α)
deriving DecidableEq

@[ext] theorem HybridState.ext {α : Type*} {left right : HybridState α}
    (hAmbient : left.ambient = right.ambient)
    (hPositive : left.positive = right.positive)
    (hNegative : left.negative = right.negative) : left = right := by
  cases left
  cases right
  simp_all

noncomputable def accumulatedHybridState {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) : HybridState (StagedProductVertex r b) where
  ambient := accumulatedStagedRegion processed blockAt choiceAt
  positive := accumulatedPositiveNormalForm processed blockAt
  negative := filterWithin (blocker (stagedProductFamily r b))
    (accumulatedStagedRegion processed blockAt choiceAt)

noncomputable def finalHybridStates (r b : Nat) :
    Finset (HybridState (StagedProductVertex r b)) :=
  (Finset.univ : Finset (Fin r → Fin b × (Fin b → Bool))).image fun codeAt =>
    accumulatedHybridState Finset.univ
      (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)

theorem finalHybridStateMap_injective {r b : Nat} :
    Function.Injective (fun codeAt : Fin r → Fin b × (Fin b → Bool) =>
      accumulatedHybridState Finset.univ
        (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)) := by
  intro left right hStates
  apply finalAccumulatedRegion_injective
  exact congrArg HybridState.ambient hStates

theorem finalHybridStates_card (r b : Nat) :
    (finalHybridStates r b).card = (b * 2 ^ b) ^ r := by
  classical
  rw [finalHybridStates,
    Finset.card_image_iff.mpr fun left _ right _ h =>
      finalHybridStateMap_injective h]
  simp

/-- The component's exponential edge count dominates its `4b` blocker size
from the first parameter value used by the obstruction. -/
theorem four_mul_lt_two_pow {b : Nat} (hb : 5 ≤ b) : 4 * b < 2 ^ b := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ b hb ih =>
      rw [pow_succ]
      have hsmall : 4 < 2 ^ b := by omega
      omega

theorem accumulatedPositive_size_gt_four_mul {r b : Nat}
    (processed : Finset (Fin r)) (stage : Fin r)
    (hstage : stage ∉ processed) (hb : 5 ≤ b) :
    4 * b < processed.card + (r - processed.card) * 2 ^ b := by
  have hcard : processed.card < r :=
    processed_card_lt_of_stage_not_mem processed stage hstage
  have hremaining : 1 ≤ r - processed.card := by omega
  have hpow : 4 * b < 2 ^ b := four_mul_lt_two_pow hb
  have hle : 2 ^ b ≤ (r - processed.card) * 2 ^ b := by
    nlinarith [show 0 < 2 ^ b by positivity]
  omega

/-- A certified positive strong-cover transition of the frequency hybrid.
The witnesses record the exact branch checks used by the algorithm. -/
def CanonicalHybridBranchStep {r b : Nat} (ω : ℝ)
    (parent child : HybridState (StagedProductVertex r b)) : Prop :=
  ∃ (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
      (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
      (block : Fin b) (choice : Fin b → Bool),
    stage ∉ processed ∧
    parent = accumulatedHybridState processed blockAt choiceAt ∧
    ¬ HasFrequentPivot parent.positive parent.negative ω ∧
    IsPositiveBranchCandidate parent.positive ω (selectedStagedEdge stage) ∧
    accumulatedStagedRegion processed blockAt choiceAt ∩
        stagedCoverRegion stage block choice ∈
      strongMemberFullCoverWithin parent.ambient parent.positive
        (selectedStagedEdge stage) ∧
    child = accumulatedHybridState (insert stage processed)
      (Function.update blockAt stage block)
      (Function.update choiceAt stage choice)

theorem canonicalHybridBranchStep_of_not_mem {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (stage : Fin r)
    (hstage : stage ∉ processed) (block : Fin b)
    (choice : Fin b → Bool) (ω : ℝ) (hb : 5 ≤ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    CanonicalHybridBranchStep ω
      (accumulatedHybridState processed blockAt choiceAt)
      (accumulatedHybridState (insert stage processed)
        (Function.update blockAt stage block)
        (Function.update choiceAt stage choice)) := by
  have hpositive : 0 < b := by omega
  have hsize := accumulatedPositive_size_gt_four_mul
    processed stage hstage hb
  refine ⟨processed, blockAt, choiceAt, stage, block, choice,
    hstage, rfl, ?_, ?_, ?_, rfl⟩
  · exact accumulated_hasNoFrequentPivot processed blockAt choiceAt ω
      hpositive hsize hlower
  · exact unprocessedStage_isPositiveBranchCandidate processed blockAt stage
      hstage (selectedProductEdge b) (selectedProductEdge_mem_family b)
      ω hpositive hupper
  · apply Finset.mem_image.mpr
    exact ⟨stagedCoverRegion stage block choice,
      stagedCoverRegion_mem_accumulatedStrongCover
        processed blockAt stage hstage block choice, rfl⟩

theorem accumulatedHybridState_reachable {r b : Nat}
    (processed : Finset (Fin r)) (blockAt : Fin r → Fin b)
    (choiceAt : Fin r → Fin b → Bool) (ω : ℝ) (hb : 5 ≤ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    Relation.ReflTransGen (CanonicalHybridBranchStep ω)
      (accumulatedHybridState ∅ blockAt choiceAt)
      (accumulatedHybridState processed blockAt choiceAt) := by
  induction processed using Finset.induction with
  | empty => exact Relation.ReflTransGen.refl
  | @insert stage processed hstage ih =>
      apply ih.tail
      have hstep := canonicalHybridBranchStep_of_not_mem
        processed blockAt choiceAt stage hstage (blockAt stage)
          (choiceAt stage) ω hb hlower hupper
      simpa [Function.update] using hstep

noncomputable def rootHybridState (r b : Nat) :
    HybridState (StagedProductVertex r b) where
  ambient := Finset.univ
  positive := stagedProductFamily r b
  negative := blocker (stagedProductFamily r b)

theorem accumulatedHybridState_empty {r b : Nat}
    (blockAt : Fin r → Fin b) (choiceAt : Fin r → Fin b → Bool) :
    accumulatedHybridState ∅ blockAt choiceAt = rootHybridState r b := by
  classical
  apply HybridState.ext <;>
    simp [accumulatedHybridState, rootHybridState, accumulatedStagedRegion,
      accumulatedPositiveNormalForm, processedSingletonFamily,
      stagedProductFamilyOutside, stagedProductFamily, filterWithin]

theorem finalHybridState_reachable {r b : Nat}
    (codeAt : Fin r → Fin b × (Fin b → Bool)) (ω : ℝ) (hb : 5 ≤ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    Relation.ReflTransGen (CanonicalHybridBranchStep ω)
      (rootHybridState r b)
      (accumulatedHybridState Finset.univ
        (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)) := by
  rw [← accumulatedHybridState_empty
    (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)]
  exact accumulatedHybridState_reachable Finset.univ
    (fun stage => (codeAt stage).1) (fun stage => (codeAt stage).2)
    ω hb hlower hupper

theorem finalHybridStates_all_reachable {r b : Nat} (ω : ℝ) (hb : 5 ≤ b)
    (hlower : (1 : ℝ) / (4 * b) < ω)
    (hupper : ω ≤ (1 : ℝ) / (2 * r)) :
    ∀ state ∈ finalHybridStates r b,
      Relation.ReflTransGen (CanonicalHybridBranchStep ω)
        (rootHybridState r b) state := by
  intro state hstate
  obtain ⟨codeAt, _, rfl⟩ := Finset.mem_image.mp hstate
  exact finalHybridState_reachable codeAt ω hb hlower hupper

def rootCardinalityVolume (r b : Nat) : Nat :=
  (r * 2 ^ b) * (4 * b) ^ r

theorem rootCardinalityVolume_eq (r b : Nat) (hb : 0 < b) :
    rootCardinalityVolume r b =
      (stagedProductFamily r b).card *
        (blocker (stagedProductFamily r b)).card := by
  classical
  let blockAt : Fin r → Fin b := fun _ => ⟨0, hb⟩
  have hout : stagedProductFamilyOutside (b := b) ∅ =
      stagedProductFamily r b := by
    ext A
    simp [stagedProductFamilyOutside, stagedProductFamily]
  have hfamily : (stagedProductFamily r b).card = r * 2 ^ b := by
    rw [← hout]
    simpa using stagedProductFamilyOutside_card
      (processed := (∅ : Finset (Fin r))) blockAt
  rw [rootCardinalityVolume, hfamily, stagedProduct_blocker_card]

theorem nat_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

theorem four_mul_sq_le_two_pow_four_mul {r : Nat} (hr : 1 ≤ r) :
    4 * r ^ 2 ≤ 2 ^ (4 * r) := by
  have hrpow : r ≤ 2 ^ r := nat_le_two_pow r
  have hsquare : r ^ 2 ≤ (2 ^ r) ^ 2 := by nlinarith
  calc
    4 * r ^ 2 ≤ 4 * (2 ^ r) ^ 2 := Nat.mul_le_mul_left 4 hsquare
    _ = 2 ^ (2 + 2 * r) := by
      rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ 2 ^ (4 * r) :=
      Nat.pow_le_pow_right (by omega) (by omega)

theorem squareParameter_rootVolume_le {r : Nat} (hr : 1 ≤ r) :
    rootCardinalityVolume r (r ^ 2) ≤ 2 ^ (6 * r ^ 2) := by
  have hrpow : r ≤ 2 ^ r := nat_le_two_pow r
  have hbase : 4 * r ^ 2 ≤ 2 ^ (4 * r) :=
    four_mul_sq_le_two_pow_four_mul hr
  have hfactor : (4 * r ^ 2) ^ r ≤ (2 ^ (4 * r)) ^ r :=
    Nat.pow_le_pow_left hbase r
  calc
    rootCardinalityVolume r (r ^ 2) =
        (r * 2 ^ (r ^ 2)) * (4 * r ^ 2) ^ r := rfl
    _ ≤ ((2 ^ r) * 2 ^ (r ^ 2)) * (2 ^ (4 * r)) ^ r :=
      Nat.mul_le_mul (Nat.mul_le_mul hrpow le_rfl) hfactor
    _ = 2 ^ (r + r ^ 2 + 4 * r ^ 2) := by
      rw [← pow_mul, ← pow_add, ← pow_add]
      congr 1
      ring
    _ ≤ 2 ^ (6 * r ^ 2) := by
      apply Nat.pow_le_pow_right (by omega)
      have hrsq : r ≤ r ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right r hr
      omega

theorem squareParameter_stateCount_ge (r : Nat) :
    2 ^ (r ^ 3) ≤ ((r ^ 2) * 2 ^ (r ^ 2)) ^ r := by
  by_cases hr : r = 0
  · subst r
    norm_num
  calc
    2 ^ (r ^ 3) = (2 ^ (r ^ 2)) ^ r := by
      rw [show r ^ 3 = r ^ 2 * r by ring, pow_mul]
    _ ≤ ((r ^ 2) * 2 ^ (r ^ 2)) ^ r := by
      apply Nat.pow_le_pow_left
      exact Nat.le_mul_of_pos_left _ (by positivity)

/-- The certified reachable-state count defeats every fixed polynomial in
the root input/output cardinality volume. -/
theorem squareParameter_superpolynomial (degree : Nat) :
    let r := 6 * degree + 2
    let b := r ^ 2
    rootCardinalityVolume r b ^ degree < (b * 2 ^ b) ^ r := by
  dsimp
  let r := 6 * degree + 2
  have hr : 1 ≤ r := by simp [r]
  have hvolume := squareParameter_rootVolume_le hr
  have hvolumePow : rootCardinalityVolume r (r ^ 2) ^ degree ≤
      (2 ^ (6 * r ^ 2)) ^ degree := Nat.pow_le_pow_left hvolume degree
  have hexponent : 6 * r ^ 2 * degree < r ^ 3 := by
    have hrd : 6 * degree < r := by simp [r]
    calc
      6 * r ^ 2 * degree = r ^ 2 * (6 * degree) := by ring
      _ < r ^ 2 * r := Nat.mul_lt_mul_of_pos_left hrd (by positivity)
      _ = r ^ 3 := by ring
  have hpowers : (2 ^ (6 * r ^ 2)) ^ degree < 2 ^ (r ^ 3) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) hexponent
  exact (hvolumePow.trans_lt hpowers).trans_le
    (squareParameter_stateCount_ge r)

noncomputable def thresholdKernel (x : ℝ) : ℝ := (x / 2) ^ x

theorem thresholdKernel_strictMonoOn :
    StrictMonoOn thresholdKernel (Set.Ici (2 : ℝ)) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hbaseNonneg : 0 ≤ x / 2 := by positivity
  have hbaseLt : x / 2 < y / 2 := by linarith
  have hy' : (2 : ℝ) ≤ y := hy
  have hybase : 1 ≤ y / 2 := by linarith
  exact (Real.rpow_lt_rpow hbaseNonneg hbaseLt hxpos).trans_le
    (Real.rpow_le_rpow_of_exponent_le hybase hxy.le)

theorem thresholdKernel_two_mul_nat (n : Nat) :
    thresholdKernel (2 * n) = (n ^ (2 * n) : Nat) := by
  unfold thresholdKernel
  norm_num
  have hexponent : (2 : ℝ) * n = ((2 * n : Nat) : ℝ) := by norm_num
  rw [hexponent, Real.rpow_natCast]

/-- Continuous threshold used by the hybrid analysis: `ω=1/χ`, where
`(χ/2)^χ` is the cardinality volume and `χ` lies in the monotone regime. -/
def IsTheoreticalThreshold (volume : Nat) (ω : ℝ) : Prop :=
  ∃ χ : ℝ, 2 ≤ χ ∧ thresholdKernel χ = volume ∧ ω = 1 / χ

theorem theoreticalThreshold_mem_interval {r b volume : Nat} {ω : ℝ}
    (hr : 1 ≤ r) (hvolumeLower : r ^ (2 * r) ≤ volume)
    (hvolumeUpper : volume < (2 * b) ^ (4 * b))
    (hthreshold : IsTheoreticalThreshold volume ω) :
    (1 : ℝ) / (4 * b) < ω ∧ ω ≤ (1 : ℝ) / (2 * r) := by
  obtain ⟨χ, hχtwo, hχvolume, rfl⟩ := hthreshold
  have htwoR : (2 : ℝ) ≤ 2 * r := by exact_mod_cast (by omega : 2 ≤ 2 * r)
  have hχLower : (2 * r : ℝ) ≤ χ := by
    by_contra hnot
    have hlt : χ < 2 * r := lt_of_not_ge hnot
    have hklt := thresholdKernel_strictMonoOn hχtwo htwoR hlt
    have hcastLower : (r ^ (2 * r) : Nat) ≤ (volume : ℝ) := by
      exact_mod_cast hvolumeLower
    rw [thresholdKernel_two_mul_nat, hχvolume] at hklt
    linarith
  have hχUpper : χ < (4 * b : ℝ) := by
    by_contra hnot
    have hle : (4 * b : ℝ) ≤ χ := le_of_not_gt hnot
    have hfourB : (2 : ℝ) ≤ 4 * b := by
      have hb : 0 < b := by
        by_contra hbzero
        have : b = 0 := Nat.eq_zero_of_not_pos hbzero
        subst b
        have hone : 1 ≤ r ^ (2 * r) := Nat.one_le_pow (2 * r) r hr
        norm_num at hvolumeUpper
        omega
      exact_mod_cast (by omega : 2 ≤ 4 * b)
    have hkle := (thresholdKernel_strictMonoOn.monotoneOn hfourB hχtwo hle)
    have hcastUpper : (volume : ℝ) < ((2 * b) ^ (4 * b) : Nat) := by
      exact_mod_cast hvolumeUpper
    have hkfour : thresholdKernel (4 * (b : ℝ)) =
        (((2 * b) ^ (4 * b) : Nat) : ℝ) := by
      convert thresholdKernel_two_mul_nat (2 * b) using 1 <;> norm_num <;> ring_nf
    rw [hkfour, hχvolume] at hkle
    linarith
  have hχpos : 0 < χ := lt_of_lt_of_le (by norm_num) hχtwo
  constructor
  · exact one_div_lt_one_div_of_lt hχpos hχUpper
  · exact one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * r) hχLower

theorem squareParameter_rootVolume_lower {r : Nat} (hr : 1 ≤ r) :
    r ^ (2 * r) ≤ rootCardinalityVolume r (r ^ 2) := by
  have hbase : r ≤ 2 * r := by omega
  have hpowers : r ^ (2 * r) ≤ (2 * r) ^ (2 * r) :=
    Nat.pow_le_pow_left hbase (2 * r)
  have heq : (2 * r) ^ (2 * r) = (4 * r ^ 2) ^ r := by
    calc
      (2 * r) ^ (2 * r) = ((2 * r) ^ 2) ^ r := pow_mul _ _ _
      _ = (4 * r ^ 2) ^ r := by
        congr 1
        ring
  have hmult : (4 * r ^ 2) ^ r ≤
      (r * 2 ^ (r ^ 2)) * (4 * r ^ 2) ^ r :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by positivity))
  exact hpowers.trans_eq heq |>.trans hmult

theorem squareParameter_rootVolume_upper {r : Nat} (hr : 2 ≤ r) :
    rootCardinalityVolume r (r ^ 2) <
      (2 * r ^ 2) ^ (4 * r ^ 2) := by
  have hvolume := squareParameter_rootVolume_le (by omega : 1 ≤ r)
  have hexp : 6 * r ^ 2 < 8 * r ^ 2 := by nlinarith
  have hpowers : 2 ^ (6 * r ^ 2) < 2 ^ (8 * r ^ 2) :=
    Nat.pow_lt_pow_right (by omega) hexp
  have hbase : 4 ≤ 2 * r ^ 2 := by nlinarith
  have hlast : 4 ^ (4 * r ^ 2) ≤ (2 * r ^ 2) ^ (4 * r ^ 2) :=
    Nat.pow_le_pow_left hbase _
  have heq : 2 ^ (8 * r ^ 2) = 4 ^ (4 * r ^ 2) := by
    rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
    ring
  exact (hvolume.trans_lt hpowers).trans_eq heq |>.trans_le hlast

theorem squareParameter_theoreticalThreshold_interval {r : Nat} {ω : ℝ}
    (hr : 2 ≤ r)
    (hthreshold : IsTheoreticalThreshold
      (rootCardinalityVolume r (r ^ 2)) ω) :
    (1 : ℝ) / (4 * r ^ 2) < ω ∧ ω ≤ (1 : ℝ) / (2 * r) := by
  simpa [Nat.cast_pow] using theoreticalThreshold_mem_interval (by omega : 1 ≤ r)
    (squareParameter_rootVolume_lower (by omega : 1 ≤ r))
    (squareParameter_rootVolume_upper hr) hthreshold

/-- At its cardinality-defined threshold, the canonical frequency/strong-cover
hybrid has more reachable memo states than every fixed polynomial in its root
cardinality volume.  This rules out an output-polynomial analysis of this
particular recursion and tie-breaking rule. -/
theorem theoreticalThreshold_hybrid_superpolynomial (degree : Nat) {ω : ℝ}
    (hdegree : 1 ≤ degree)
    (hthreshold : IsTheoreticalThreshold
      (rootCardinalityVolume (6 * degree + 2) ((6 * degree + 2) ^ 2)) ω) :
    (∀ state ∈ finalHybridStates (6 * degree + 2) ((6 * degree + 2) ^ 2),
        Relation.ReflTransGen (CanonicalHybridBranchStep ω)
          (rootHybridState (6 * degree + 2) ((6 * degree + 2) ^ 2)) state) ∧
      (finalHybridStates (6 * degree + 2) ((6 * degree + 2) ^ 2)).card =
        (((6 * degree + 2) ^ 2) * 2 ^ ((6 * degree + 2) ^ 2)) ^
          (6 * degree + 2) ∧
      rootCardinalityVolume (6 * degree + 2) ((6 * degree + 2) ^ 2) ^ degree <
        (finalHybridStates (6 * degree + 2) ((6 * degree + 2) ^ 2)).card := by
  have hr : 2 ≤ 6 * degree + 2 := by omega
  have hr3 : 3 ≤ 6 * degree + 2 := by omega
  have hsquare := Nat.pow_le_pow_left hr3 2
  have hb : 5 ≤ (6 * degree + 2) ^ 2 := by omega
  obtain ⟨hlower, hupper⟩ :=
    squareParameter_theoreticalThreshold_interval hr hthreshold
  have hlower' : (1 : ℝ) / (4 * ((6 * degree + 2) ^ 2 : Nat)) < ω := by
    simpa [Nat.cast_pow] using hlower
  refine ⟨finalHybridStates_all_reachable ω hb hlower' hupper,
    finalHybridStates_card _ _, ?_⟩
  rw [finalHybridStates_card]
  exact squareParameter_superpolynomial degree

end IrrRAFEnumeration

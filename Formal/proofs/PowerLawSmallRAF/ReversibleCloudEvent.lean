import proofs.PowerLawSmallRAF.ReversibleCloudCertificates
import proofs.PowerLawSmallRAF.ReversibleStoppedTrace

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

noncomputable def cloudFirstHitCertificateLayer
    {n k s : Nat} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat) :
    Finset (Fin (sourceMoleculeCount n) ×
      VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) :=
  (Finset.univ : Finset (ReversibleFirstHitCode n s)).biUnion fun code =>
    {reversibleFirstHitOutput hs code} ×ˢ
      mappedVariableContainmentCertificateEvent
        (fun i => degree i - 1) (traceCloudRequired gateway code.1)
        (cloudNongatewayChannel hn gateway)

theorem supported_firstHit_mem_cloudFirstHitCertificateLayer
    {n k s : Nat} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat)
    (code : ReversibleFirstHitCode n s)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
    (htrace : code.1.val.toFinset ⊆
      gatewayCloudReactionSet hn gateway degree config) :
    (reversibleFirstHitOutput hs code, config) ∈
      cloudFirstHitCertificateLayer hn hs gateway degree := by
  simp only [cloudFirstHitCertificateLayer, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨code, ?_⟩
  simp only [Finset.mem_product, Finset.mem_singleton, true_and]
  exact supported_trace_mem_mappedVariableContainmentCertificateEvent
    hn gateway degree code.1 config htrace

theorem cloudFirstHitCertificateLayer_uniformMass_le
    {n k s D : Nat} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat)
    (hdegree : ∀ i, degree i ≤ D + 1) (hsD : s ≤ D)
    (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : (k : ℝ) * D /
      (sourceReactionCount n - 1 - s + 1 : Nat) ≤ 1) :
    ((cloudFirstHitCertificateLayer hn hs gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
        sourceMoleculeCount n *
          (((k : ℝ) * D /
            (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k)) := by
  let configCard := Fintype.card
    (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
  let base : ℝ := (k : ℝ) * D /
    (sourceReactionCount n - 1 - s + 1 : Nat)
  have hX : 0 < sourceMoleculeCount n := by
    exact (pow_pos (by norm_num) n).trans_le
      (sourceMoleculeCount_bounds (by omega)).1
  have hden : 0 ≤ (sourceMoleculeCount n : ℝ) * (configCard : ℝ) := by
    positivity
  have hcard : (cloudFirstHitCertificateLayer hn hs gateway degree).card ≤
      ∑ code : ReversibleFirstHitCode n s,
        ({reversibleFirstHitOutput hs code} ×ˢ
          mappedVariableContainmentCertificateEvent
            (fun i => degree i - 1) (traceCloudRequired gateway code.1)
            (cloudNongatewayChannel hn gateway)).card :=
    Finset.card_biUnion_le
  calc
    ((cloudFirstHitCertificateLayer hn hs gateway degree).card : ℝ) /
        (sourceMoleculeCount n * configCard) ≤
      ((∑ code : ReversibleFirstHitCode n s,
        ({reversibleFirstHitOutput hs code} ×ˢ
          mappedVariableContainmentCertificateEvent
            (fun i => degree i - 1) (traceCloudRequired gateway code.1)
            (cloudNongatewayChannel hn gateway)).card : Nat) : ℝ) /
        (sourceMoleculeCount n * configCard) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = ∑ code : ReversibleFirstHitCode n s,
        ((mappedVariableContainmentCertificateEvent
          (fun i => degree i - 1) (traceCloudRequired gateway code.1)
          (cloudNongatewayChannel hn gateway)).card : ℝ) /
            (sourceMoleculeCount n * configCard) := by
      push_cast
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro code hcode
      rw [Finset.card_product, Finset.card_singleton]
      norm_num
    _ ≤ ∑ _code : ReversibleFirstHitCode n s,
        base ^ (s - k) / sourceMoleculeCount n := by
      apply Finset.sum_le_sum
      intro code hcode
      have htraceBound := traceCloudCertificate_uniformMass_le hn gateway degree
        code.1 hdegree hsD hDR hbase
      dsimp only [configCard, base]
      have hXreal : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
      have hCreal : (Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1)) : ℝ) ≠ 0 := by
        apply Nat.cast_ne_zero.mpr
        have hC : 0 < Fintype.card
            (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
              (fun i => degree i - 1)) := by
          rw [Fintype.card_pi]
          apply Finset.prod_pos
          intro i hi
          rw [card_fixedSizeFibre]
          exact Nat.choose_pos
            ((Nat.sub_le_of_le_add (hdegree i)).trans hDR)
        exact hC.ne'
      rw [show (((mappedVariableContainmentCertificateEvent
          (fun i => degree i - 1) (traceCloudRequired gateway code.1)
          (cloudNongatewayChannel hn gateway)).card : ℝ) /
          (sourceMoleculeCount n * Fintype.card
            (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
              (fun i => degree i - 1)))) =
          (((mappedVariableContainmentCertificateEvent
            (fun i => degree i - 1) (traceCloudRequired gateway code.1)
            (cloudNongatewayChannel hn gateway)).card : ℝ) /
            Fintype.card (VariableFixedSizeFibreConfig
              (sourceReactionCount n - 1) (fun i => degree i - 1))) /
            sourceMoleculeCount n by field_simp]
      exact div_le_div_of_nonneg_right htraceBound (by positivity)
    _ = (Fintype.card (ReversibleFirstHitCode n s) : ℝ) /
        sourceMoleculeCount n * base ^ (s - k) := by
      simp
      ring
    _ ≤ ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
        sourceMoleculeCount n * base ^ (s - k) := by
      apply mul_le_mul_of_nonneg_right
      · apply div_le_div_of_nonneg_right (by
          exact_mod_cast card_reversibleFirstHitCode_le n s hsn) (by positivity)
      · positivity

/-- Degree-free first-hit envelope.  When the trace length is no larger than
the owner count, the useful charge is not a containment moment but the
uniform endpoint label: every trace code contributes at most the whole fibre
configuration space, hence the layer costs only its grammar count divided by
the molecule catalogue size. -/
theorem cloudFirstHitCertificateLayer_uniformMass_le_codeCount
    {n k s : Nat} (hn : 2 ≤ n) (hs : 1 ≤ s) (hsn : s ≤ n)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat) :
    ((cloudFirstHitCertificateLayer hn hs gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
        sourceMoleculeCount n := by
  let configCard := Fintype.card
    (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
  have hX : 0 < sourceMoleculeCount n := by
    exact (pow_pos (by norm_num) n).trans_le
      (sourceMoleculeCount_bounds (by omega)).1
  have hcard : (cloudFirstHitCertificateLayer hn hs gateway degree).card ≤
      Fintype.card (ReversibleFirstHitCode n s) * configCard := by
    calc
      (cloudFirstHitCertificateLayer hn hs gateway degree).card ≤
          ∑ code : ReversibleFirstHitCode n s,
            ({reversibleFirstHitOutput hs code} ×ˢ
              mappedVariableContainmentCertificateEvent
                (fun i => degree i - 1) (traceCloudRequired gateway code.1)
                (cloudNongatewayChannel hn gateway)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _code : ReversibleFirstHitCode n s, configCard := by
        apply Finset.sum_le_sum
        intro code _
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact Finset.card_le_univ _
      _ = Fintype.card (ReversibleFirstHitCode n s) * configCard := by simp
  by_cases hconfig0 : configCard = 0
  · have hlayer : (cloudFirstHitCertificateLayer hn hs gateway degree).card = 0 := by
      have hle : (cloudFirstHitCertificateLayer hn hs gateway degree).card ≤ 0 := by
        simpa [hconfig0] using hcard
      omega
    rw [hlayer]
    simp only [Nat.cast_zero, zero_div]
    positivity
  have hconfig : 0 < configCard := Nat.pos_of_ne_zero hconfig0
  have hden : 0 ≤ (sourceMoleculeCount n : ℝ) * configCard := by positivity
  calc
    ((cloudFirstHitCertificateLayer hn hs gateway degree).card : ℝ) /
        (sourceMoleculeCount n * configCard) ≤
      ((Fintype.card (ReversibleFirstHitCode n s) * configCard : Nat) : ℝ) /
        (sourceMoleculeCount n * configCard) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = (Fintype.card (ReversibleFirstHitCode n s) : ℝ) /
        sourceMoleculeCount n := by
      push_cast
      field_simp
    _ ≤ ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
        sourceMoleculeCount n := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast card_reversibleFirstHitCode_le n s hsn)
        (by positivity)

noncomputable def cloudSurvivalCertificateEvent
    {n k : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) :
    Finset (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1)) :=
  (Finset.univ : Finset (ReversibleTraceCode n n)).biUnion fun code =>
    mappedVariableContainmentCertificateEvent
      (fun i => degree i - 1) (traceCloudRequired gateway code)
      (cloudNongatewayChannel hn gateway)

theorem supported_survival_mem_cloudSurvivalCertificateEvent
    {n k : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (code : ReversibleTraceCode n n)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
    (htrace : code.val.toFinset ⊆
      gatewayCloudReactionSet hn gateway degree config) :
    config ∈ cloudSurvivalCertificateEvent hn gateway degree := by
  simp only [cloudSurvivalCertificateEvent, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  exact ⟨code, supported_trace_mem_mappedVariableContainmentCertificateEvent
    hn gateway degree code config htrace⟩

theorem cloudSurvivalCertificateEvent_uniformMass_le
    {n k D : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (hdegree : ∀ i, degree i ≤ D + 1)
    (hnD : n ≤ D) (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : (k : ℝ) * D /
      (sourceReactionCount n - 1 - n + 1 : Nat) ≤ 1) :
    ((cloudSurvivalCertificateEvent hn gateway degree).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig
          (sourceReactionCount n - 1) (fun i => degree i - 1)) ≤
      ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
        (((k : ℝ) * D /
          (sourceReactionCount n - 1 - n + 1 : Nat)) ^ (n - k)) := by
  let configCard := Fintype.card
    (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
  let base : ℝ := (k : ℝ) * D /
    (sourceReactionCount n - 1 - n + 1 : Nat)
  have hden : 0 ≤ (configCard : ℝ) := by positivity
  have hcard : (cloudSurvivalCertificateEvent hn gateway degree).card ≤
      ∑ code : ReversibleTraceCode n n,
        (mappedVariableContainmentCertificateEvent
          (fun i => degree i - 1) (traceCloudRequired gateway code)
          (cloudNongatewayChannel hn gateway)).card :=
    Finset.card_biUnion_le
  calc
    ((cloudSurvivalCertificateEvent hn gateway degree).card : ℝ) / configCard ≤
      ((∑ code : ReversibleTraceCode n n,
        (mappedVariableContainmentCertificateEvent
          (fun i => degree i - 1) (traceCloudRequired gateway code)
          (cloudNongatewayChannel hn gateway)).card : Nat) : ℝ) / configCard := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = ∑ code : ReversibleTraceCode n n,
        ((mappedVariableContainmentCertificateEvent
          (fun i => degree i - 1) (traceCloudRequired gateway code)
          (cloudNongatewayChannel hn gateway)).card : ℝ) / configCard := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ _code : ReversibleTraceCode n n, base ^ (n - k) := by
      apply Finset.sum_le_sum
      intro code hcode
      exact traceCloudCertificate_uniformMass_le hn gateway degree code
        hdegree hnD hDR hbase
    _ = (Fintype.card (ReversibleTraceCode n n) : ℝ) * base ^ (n - k) := by
      simp
    _ ≤ ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
        base ^ (n - k) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_reversibleTraceCode_le n n (le_refl n)
      · positivity

theorem source_cloud_reachability_firstHit_or_survival
    {n k t : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1)) {x : Molecule n}
    (hxFood : x ∉ binaryFood n 2)
    (hxReachable : x ∈ revClosureAt (binaryPolymerCRS n 2)
      (gatewayCloudReactionSet hn gateway degree config) t) :
    (∃ (s : Nat) (hs : 1 ≤ s) (_hsn : s ≤ n)
        (code : ReversibleTraceCode n s) (selector : Fin 2),
      reversibleFirstHitOutput hs (code, selector) =
        binaryMoleculeEquivFin n x ∧
      code.val.toFinset ⊆ gatewayCloudReactionSet hn gateway degree config) ∨
    (∃ code : ReversibleTraceCode n n,
      code.val.toFinset ⊆ gatewayCloudReactionSet hn gateway degree config) := by
  obtain ⟨trace, htrace, htraceSubset, _htraceLength, hxFinal⟩ :=
    source_reversible_reachability_has_counted_trace
      (gatewayCloudReactionSet hn gateway degree config) hxReachable
  obtain ⟨s, hs, hsLength, hxHit, hxPrevious⟩ :=
    exists_first_hit_prefix (binaryFood n 2) trace hxFood hxFinal
  by_cases hsn : s ≤ n
  · left
    have hprefix : trace.take s ∈
        reversibleTraceFinset (binaryFood n 2) s :=
      take_mem_reversibleTraceFinset htrace hsLength
    let code : ReversibleTraceCode n s := ⟨trace.take s, hprefix⟩
    have hxPrevious' : x ∉ reversibleTraceAvailable (binaryFood n 2)
        code.val.dropLast := by
      simpa only [code, dropLast_take_eq_take_pred trace hs hsLength] using
        hxPrevious
    obtain ⟨selector, houtput⟩ :=
      exists_selector_reversibleFirstHitOutput_eq hs code hxHit hxPrevious'
    refine ⟨s, hs, hsn, code, selector, houtput, ?_⟩
    exact (toFinset_take_subset trace s).trans htraceSubset
  · have hnLength : n ≤ trace.length := by omega
    have hprefix : trace.take n ∈
        reversibleTraceFinset (binaryFood n 2) n :=
      take_mem_reversibleTraceFinset htrace hnLength
    let code : ReversibleTraceCode n n := ⟨trace.take n, hprefix⟩
    exact Or.inr ⟨code, (toFinset_take_subset trace n).trans htraceSubset⟩

noncomputable def canonicalCloudFirstHitEvent
    {n k : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) :
    Finset (Fin (sourceMoleculeCount n) ×
      VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) :=
  (Finset.Icc 1 n).biUnion fun s =>
    if hs : 1 ≤ s then cloudFirstHitCertificateLayer hn hs gateway degree else ∅

noncomputable def canonicalCloudFoodPairEvent
    {n k : Nat} (degree : Fin k → Nat) :
    Finset (Fin (sourceMoleculeCount n) ×
      VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) :=
  ((binaryFood n 2).image (binaryMoleculeEquivFin n)).product Finset.univ

noncomputable def canonicalCloudSurvivalPairEvent
    {n k : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) :
    Finset (Fin (sourceMoleculeCount n) ×
      VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) :=
  Finset.univ.product (cloudSurvivalCertificateEvent hn gateway degree)

noncomputable def canonicalCloudSelfGenerationEvent
    {n k : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) :
    Finset (Fin (sourceMoleculeCount n) ×
      VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) :=
  canonicalCloudFoodPairEvent degree ∪
    (canonicalCloudFirstHitEvent hn gateway degree ∪
      canonicalCloudSurvivalPairEvent hn gateway degree)

theorem source_cloud_reachable_mem_selfGenerationEvent
    {n k t : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1)) {x : Molecule n}
    (hxReachable : x ∈ revClosureAt (binaryPolymerCRS n 2)
      (gatewayCloudReactionSet hn gateway degree config) t) :
    (binaryMoleculeEquivFin n x, config) ∈
      canonicalCloudSelfGenerationEvent hn gateway degree := by
  by_cases hxFood : x ∈ binaryFood n 2
  · simp [canonicalCloudSelfGenerationEvent, canonicalCloudFoodPairEvent,
      hxFood]
  · rcases source_cloud_reachability_firstHit_or_survival
      hn gateway degree config hxFood hxReachable with hfirst | hsurvival
    · obtain ⟨s, hs, hsn, code, selector, houtput, htrace⟩ := hfirst
      simp only [canonicalCloudSelfGenerationEvent, Finset.mem_union]
      right
      left
      simp only [canonicalCloudFirstHitEvent, Finset.mem_biUnion]
      refine ⟨s, Finset.mem_Icc.mpr ⟨hs, hsn⟩, ?_⟩
      rw [dif_pos hs, ← houtput]
      exact supported_firstHit_mem_cloudFirstHitCertificateLayer
        hn hs gateway degree (code, selector) config htrace
    · obtain ⟨code, htrace⟩ := hsurvival
      simp [canonicalCloudSelfGenerationEvent,
        canonicalCloudSurvivalPairEvent,
        supported_survival_mem_cloudSurvivalCertificateEvent
          hn gateway degree code config htrace]

theorem canonicalCloudFirstHitEvent_uniformMass_le
    {n k D : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (hdegree : ∀ i, degree i ≤ D + 1)
    (hnD : n ≤ D) (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : ∀ s ≤ n, (k : ℝ) * D /
      (sourceReactionCount n - 1 - s + 1 : Nat) ≤ 1) :
    ((canonicalCloudFirstHitEvent hn gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      ∑ s ∈ Finset.Icc 1 n,
        ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
          sourceMoleculeCount n *
            (((k : ℝ) * D /
              (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k)) := by
  let denominator : ℝ := sourceMoleculeCount n * Fintype.card
    (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
  have hden : 0 ≤ denominator := by positivity
  have hcard : (canonicalCloudFirstHitEvent hn gateway degree).card ≤
      ∑ s ∈ Finset.Icc 1 n,
        (if hs : 1 ≤ s then cloudFirstHitCertificateLayer hn hs gateway degree
        else ∅).card := Finset.card_biUnion_le
  calc
    ((canonicalCloudFirstHitEvent hn gateway degree).card : ℝ) / denominator ≤
      ((∑ s ∈ Finset.Icc 1 n,
        (if hs : 1 ≤ s then cloudFirstHitCertificateLayer hn hs gateway degree
        else ∅).card : Nat) : ℝ) / denominator := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = ∑ s ∈ Finset.Icc 1 n,
        (((if hs : 1 ≤ s then cloudFirstHitCertificateLayer hn hs gateway degree
        else ∅).card : Nat) : ℝ) / denominator := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ s ∈ Finset.Icc 1 n,
        ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
          sourceMoleculeCount n *
            (((k : ℝ) * D /
              (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k)) := by
      apply Finset.sum_le_sum
      intro s hsRange
      have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hsRange).1
      have hsn : s ≤ n := (Finset.mem_Icc.mp hsRange).2
      rw [dif_pos hs1]
      exact cloudFirstHitCertificateLayer_uniformMass_le hn hs1 hsn
        gateway degree hdegree (hsn.trans hnD) hDR (hbase s hsn)

theorem canonicalCloudFoodPairEvent_uniformMass_le
    {n k : Nat} (hn : 2 ≤ n) (degree : Fin k → Nat)
    (hdegreeR : ∀ i, degree i - 1 ≤ sourceReactionCount n - 1) :
    ((canonicalCloudFoodPairEvent (n := n) degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      6 / (sourceMoleculeCount n : ℝ) := by
  have hX : 0 < sourceMoleculeCount n := by
    exact (pow_pos (by norm_num) n).trans_le
      (sourceMoleculeCount_bounds (by omega)).1
  have hC : 0 < Fintype.card
      (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) := by
    rw [Fintype.card_pi]
    apply Finset.prod_pos
    intro i hi
    rw [card_fixedSizeFibre]
    exact Nat.choose_pos (hdegreeR i)
  have hfoodCard : ((binaryFood n 2).image
      (binaryMoleculeEquivFin n)).card ≤ 6 :=
    Finset.card_image_le.trans (card_binaryFood_two_le_six n)
  change (((binaryFood n 2).image (binaryMoleculeEquivFin n) ×ˢ
      (Finset.univ : Finset (VariableFixedSizeFibreConfig
        (sourceReactionCount n - 1) (fun i => degree i - 1)))).card : ℝ) /
      (sourceMoleculeCount n * Fintype.card
        (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
          (fun i => degree i - 1))) ≤ _
  rw [Finset.card_product, Finset.card_univ]
  push_cast
  have hXreal : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hCreal : (Fintype.card (VariableFixedSizeFibreConfig
      (sourceReactionCount n - 1) (fun i => degree i - 1)) : ℝ) ≠ 0 := by
    exact_mod_cast hC.ne'
  rw [show (((binaryFood n 2).image (binaryMoleculeEquivFin n)).card : ℝ) *
      Fintype.card (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
        (fun i => degree i - 1)) /
      (sourceMoleculeCount n * Fintype.card
        (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
          (fun i => degree i - 1))) =
      (((binaryFood n 2).image (binaryMoleculeEquivFin n)).card : ℝ) /
        sourceMoleculeCount n by field_simp]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hfoodCard) (by positivity)

theorem canonicalCloudSurvivalPairEvent_uniformMass_le
    {n k D : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (hdegree : ∀ i, degree i ≤ D + 1)
    (hnD : n ≤ D) (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : (k : ℝ) * D /
      (sourceReactionCount n - 1 - n + 1 : Nat) ≤ 1) :
    ((canonicalCloudSurvivalPairEvent hn gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
        (((k : ℝ) * D /
          (sourceReactionCount n - 1 - n + 1 : Nat)) ^ (n - k)) := by
  have hX : 0 < sourceMoleculeCount n := by
    exact (pow_pos (by norm_num) n).trans_le
      (sourceMoleculeCount_bounds (by omega)).1
  change (((Finset.univ : Finset (Fin (sourceMoleculeCount n))) ×ˢ
      cloudSurvivalCertificateEvent hn gateway degree).card : ℝ) /
      (sourceMoleculeCount n * Fintype.card
        (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
          (fun i => degree i - 1))) ≤ _
  rw [Finset.card_product, Finset.card_univ]
  simp only [Fintype.card_fin]
  push_cast
  have hXreal : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  have hcancel :
      (sourceMoleculeCount n : ℝ) *
          ((cloudSurvivalCertificateEvent hn gateway degree).card : ℝ) /
          ((sourceMoleculeCount n : ℝ) *
            (Fintype.card (VariableFixedSizeFibreConfig
              (sourceReactionCount n - 1) (fun i => degree i - 1)) : ℝ)) =
        ((cloudSurvivalCertificateEvent hn gateway degree).card : ℝ) /
          (Fintype.card (VariableFixedSizeFibreConfig
            (sourceReactionCount n - 1) (fun i => degree i - 1)) : ℝ) := by
    field_simp
  rw [hcancel]
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (cloudSurvivalCertificateEvent_uniformMass_le hn gateway degree
      hdegree hnD hDR hbase)

theorem canonicalCloudSelfGenerationEvent_uniformMass_le
    {n k D : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (hdegree : ∀ i, degree i ≤ D + 1)
    (hnD : n ≤ D) (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : ∀ s ≤ n, (k : ℝ) * D /
      (sourceReactionCount n - 1 - s + 1 : Nat) ≤ 1) :
    ((canonicalCloudSelfGenerationEvent hn gateway degree).card : ℝ) /
        (sourceMoleculeCount n * Fintype.card
          (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
            (fun i => degree i - 1))) ≤
      6 / (sourceMoleculeCount n : ℝ) +
        (∑ s ∈ Finset.Icc 1 n,
          ((2 * sourceReversibleBranchCount n ^ s : Nat) : ℝ) /
            sourceMoleculeCount n *
              (((k : ℝ) * D /
                (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k))) +
        ((sourceReversibleBranchCount n ^ n : Nat) : ℝ) *
          (((k : ℝ) * D /
            (sourceReactionCount n - 1 - n + 1 : Nat)) ^ (n - k)) := by
  let denominator : ℝ := sourceMoleculeCount n * Fintype.card
    (VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
  have hden : 0 ≤ denominator := by positivity
  have hdegreeR : ∀ i, degree i - 1 ≤ sourceReactionCount n - 1 := by
    intro i
    have := hdegree i
    omega
  have hcard := (Finset.card_union_le
      (canonicalCloudFoodPairEvent (n := n) degree)
      (canonicalCloudFirstHitEvent hn gateway degree ∪
        canonicalCloudSurvivalPairEvent hn gateway degree)).trans
    (Nat.add_le_add_left (Finset.card_union_le
      (canonicalCloudFirstHitEvent hn gateway degree)
      (canonicalCloudSurvivalPairEvent hn gateway degree)) _)
  calc
    ((canonicalCloudSelfGenerationEvent hn gateway degree).card : ℝ) /
        denominator ≤
      (((canonicalCloudFoodPairEvent (n := n) degree).card +
        ((canonicalCloudFirstHitEvent hn gateway degree).card +
          (canonicalCloudSurvivalPairEvent hn gateway degree).card) : Nat) : ℝ) /
        denominator := div_le_div_of_nonneg_right (by exact_mod_cast hcard) hden
    _ = ((canonicalCloudFoodPairEvent (n := n) degree).card : ℝ) / denominator +
        ((canonicalCloudFirstHitEvent hn gateway degree).card : ℝ) /
          denominator +
        ((canonicalCloudSurvivalPairEvent hn gateway degree).card : ℝ) /
          denominator := by push_cast; ring
    _ ≤ _ :=
      add_le_add
        (add_le_add
          (canonicalCloudFoodPairEvent_uniformMass_le hn degree hdegreeR)
          (canonicalCloudFirstHitEvent_uniformMass_le
            hn gateway degree hdegree hnD hDR hbase))
        (canonicalCloudSurvivalPairEvent_uniformMass_le
          hn gateway degree hdegree hnD hDR (hbase n le_rfl))

end PowerLawSmallRAF

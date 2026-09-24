import proofs.PowerLawSmallRAF.MultiFibreContainment
import proofs.PowerLawSmallRAF.CanonicalReversibleTraceCertificate

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

def gatewayRange {n k : Nat} (gateway : Fin k → Reaction n) :
    Finset (Reaction n) :=
  Finset.univ.image gateway

theorem card_gatewayRange_le {n k : Nat} (gateway : Fin k → Reaction n) :
    (gatewayRange gateway).card ≤ k := by
  rw [gatewayRange]
  exact (Finset.card_image_le.trans (by simp))

abbrev CloudNongateway {n k : Nat} (gateway : Fin k → Reaction n) :=
  {r : Reaction n // r ∉ gatewayRange gateway}

def traceCloudRequired {n k s : Nat} (gateway : Fin k → Reaction n)
    (code : ReversibleTraceCode n s) : Finset (CloudNongateway gateway) :=
  code.val.toFinset.subtype fun r => r ∉ gatewayRange gateway

theorem card_traceCloudRequired {n k s : Nat}
    (gateway : Fin k → Reaction n) (code : ReversibleTraceCode n s) :
    (traceCloudRequired gateway code).card =
      (code.val.toFinset \ gatewayRange gateway).card := by
  rw [traceCloudRequired, Finset.card_subtype]
  congr 1
  ext r
  simp

theorem card_traceCloudRequired_le {n k s : Nat}
    (gateway : Fin k → Reaction n) (code : ReversibleTraceCode n s) :
    (traceCloudRequired gateway code).card ≤ s := by
  rw [card_traceCloudRequired]
  exact (Finset.card_le_card (Finset.sdiff_subset)).trans_eq
    (by rw [List.toFinset_card_of_nodup
      (mem_reversibleTraceFinset_length_nodup code.property).2,
      (mem_reversibleTraceFinset_length_nodup code.property).1])

theorem sub_card_le_card_traceCloudRequired {n k s : Nat}
    (gateway : Fin k → Reaction n) (code : ReversibleTraceCode n s) :
    s - k ≤ (traceCloudRequired gateway code).card := by
  rw [card_traceCloudRequired]
  have htrace := mem_reversibleTraceFinset_length_nodup code.property
  have hsdiff := Finset.le_card_sdiff (gatewayRange gateway) code.val.toFinset
  rw [List.toFinset_card_of_nodup htrace.2, htrace.1] at hsdiff
  have hgate := card_gatewayRange_le gateway
  omega

theorem mem_traceCloudRequired_iff {n k s : Nat}
    (gateway : Fin k → Reaction n) (code : ReversibleTraceCode n s)
    (r : CloudNongateway gateway) :
    r ∈ traceCloudRequired gateway code ↔ r.1 ∈ code.val.toFinset := by
  simp [traceCloudRequired]

noncomputable def cloudNongatewayChannel {n k : Nat} (hn : 2 ≤ n)
    (gateway : Fin k → Reaction n) (i : Fin k) :
    CloudNongateway gateway → Fin (sourceReactionCount n - 1) := fun r =>
  binaryNongatewayReactionEquivFin hn (gateway i)
    ⟨r.1, fun heq => r.2 (by
      simp [gatewayRange, heq])⟩

theorem cloudNongatewayChannel_injective {n k : Nat} (hn : 2 ≤ n)
    (gateway : Fin k → Reaction n) (i : Fin k) :
    Function.Injective (cloudNongatewayChannel hn gateway i) := by
  intro left right h
  apply Subtype.ext
  exact congrArg (fun z : {r : Reaction n // r ≠ gateway i} => z.1)
    ((binaryNongatewayReactionEquivFin hn (gateway i)).injective h)

noncomputable def gatewayCloudReactionSet {n k : Nat} (hn : 2 ≤ n)
    (gateway : Fin k → Reaction n) (degree : Fin k → Nat)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1)) : Finset (Reaction n) :=
  Finset.univ.biUnion fun i =>
    gatewayConditionedReactionSet hn (gateway i) (config i)

theorem traceCloudRequired_covered
    {n k s : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (code : ReversibleTraceCode n s)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
    (htrace : code.val.toFinset ⊆
      gatewayCloudReactionSet hn gateway degree config) :
    ∀ r ∈ traceCloudRequired gateway code,
      ∃ i : Fin k, cloudNongatewayChannel hn gateway i r ∈ (config i).1 := by
  intro r hr
  have hrTrace : r.1 ∈ code.val.toFinset :=
    (mem_traceCloudRequired_iff gateway code r).mp hr
  have hrCloud := htrace hrTrace
  rw [gatewayCloudReactionSet, Finset.mem_biUnion] at hrCloud
  obtain ⟨i, hi, hrSet⟩ := hrCloud
  refine ⟨i, ?_⟩
  rw [gatewayConditionedReactionSet, Finset.mem_insert] at hrSet
  rcases hrSet with hgateway | himage
  · exact False.elim (r.2 (by simp [gatewayRange, hgateway]))
  · simp only [Finset.mem_image] at himage
    obtain ⟨catalogueIndex, hcatalogueIndex, heq⟩ := himage
    have hencoded : cloudNongatewayChannel hn gateway i r = catalogueIndex := by
      apply (binaryNongatewayReactionEquivFin hn (gateway i)).symm.injective
      simp only [cloudNongatewayChannel, Equiv.symm_apply_apply]
      apply Subtype.ext
      exact heq.symm
    simpa [hencoded] using hcatalogueIndex

theorem supported_trace_mem_mappedVariableContainmentCertificateEvent
    {n k s : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (code : ReversibleTraceCode n s)
    (config : VariableFixedSizeFibreConfig (sourceReactionCount n - 1)
      (fun i => degree i - 1))
    (htrace : code.val.toFinset ⊆
      gatewayCloudReactionSet hn gateway degree config) :
    config ∈ mappedVariableContainmentCertificateEvent
      (fun i => degree i - 1) (traceCloudRequired gateway code)
      (cloudNongatewayChannel hn gateway) := by
  exact mem_mappedVariableContainmentCertificateEvent_of_covered
    (fun i => degree i - 1) (traceCloudRequired gateway code)
    (cloudNongatewayChannel hn gateway) config
    (traceCloudRequired_covered hn gateway degree code config htrace)

theorem traceCloudCertificate_uniformMass_le
    {n k s D : Nat} (hn : 2 ≤ n) (gateway : Fin k → Reaction n)
    (degree : Fin k → Nat) (code : ReversibleTraceCode n s)
    (hdegree : ∀ i, degree i ≤ D + 1) (hsD : s ≤ D)
    (hDR : D ≤ sourceReactionCount n - 1)
    (hbase : (k : ℝ) * D /
      (sourceReactionCount n - 1 - s + 1 : Nat) ≤ 1) :
    ((mappedVariableContainmentCertificateEvent
      (fun i => degree i - 1) (traceCloudRequired gateway code)
      (cloudNongatewayChannel hn gateway)).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig
          (sourceReactionCount n - 1) (fun i => degree i - 1)) ≤
      ((k : ℝ) * D /
        (sourceReactionCount n - 1 - s + 1 : Nat)) ^ (s - k) := by
  let q := (traceCloudRequired gateway code).card
  apply mappedVariableContainmentCertificateEvent_coarse_le
    (fun i => degree i - 1) (traceCloudRequired gateway code) rfl
    (cloudNongatewayChannel hn gateway)
    (fun i => cloudNongatewayChannel_injective hn gateway i)
  · intro i
    exact Nat.sub_le_of_le_add (hdegree i)
  · exact (card_traceCloudRequired_le gateway code).trans hsD
  · exact hDR
  · exact card_traceCloudRequired_le gateway code
  · exact sub_card_le_card_traceCloudRequired gateway code
  · exact hbase

end PowerLawSmallRAF

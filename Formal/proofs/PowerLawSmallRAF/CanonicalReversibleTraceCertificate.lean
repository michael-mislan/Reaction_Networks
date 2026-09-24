import proofs.PowerLawSmallRAF.ReversibleTraceCertificates
import proofs.PowerLawSmallRAF.BinaryReactionEnumeration

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- Keep exactly `s-1` nongateway reactions from a nodup length-`s` trace:
delete the gateway when present, and otherwise omit the first reaction. -/
def traceNongatewayReactions {n : Nat} (gateway : Reaction n)
    (trace : List (Reaction n)) : Finset (Reaction n) :=
  if gateway ∈ trace then trace.toFinset.erase gateway else trace.tail.toFinset

theorem card_traceNongatewayReactions {n s : Nat} (gateway : Reaction n)
    (code : ReversibleTraceCode n s) :
    (traceNongatewayReactions gateway code.val).card = s - 1 := by
  have htrace := mem_reversibleTraceFinset_length_nodup code.property
  rw [traceNongatewayReactions]
  split_ifs with hg
  · rw [Finset.card_erase_of_mem (by simpa using hg),
      List.toFinset_card_of_nodup htrace.2, htrace.1]
  · rw [List.toFinset_card_of_nodup htrace.2.tail,
      List.length_tail, htrace.1]

theorem traceNongatewayReactions_subset {n : Nat} (gateway : Reaction n)
    (trace : List (Reaction n)) :
    traceNongatewayReactions gateway trace ⊆ trace.toFinset := by
  rw [traceNongatewayReactions]
  split_ifs
  · exact Finset.erase_subset _ _
  · intro r hr
    exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hr))

theorem gateway_not_mem_traceNongatewayReactions {n : Nat}
    (gateway : Reaction n) (trace : List (Reaction n)) :
    gateway ∉ traceNongatewayReactions gateway trace := by
  rw [traceNongatewayReactions]
  split_ifs with hg
  · simp
  · intro htail
    exact hg (List.mem_of_mem_tail (List.mem_toFinset.mp htail))

theorem mem_traceNongatewayReactions_ne_gateway {n : Nat}
    (gateway : Reaction n) (trace : List (Reaction n)) {r : Reaction n}
    (hr : r ∈ traceNongatewayReactions gateway trace) : r ≠ gateway := by
  intro h
  subst r
  exact gateway_not_mem_traceNongatewayReactions gateway trace hr

/-- Canonical exact nongateway catalogue requirements attached to a legal
reversible trace. -/
noncomputable def canonicalReversibleTraceRequiredChannels {n s : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n) (code : ReversibleTraceCode n s) :
    Finset (Fin (sourceReactionCount n - 1)) :=
  (traceNongatewayReactions gateway code.val).attach.image fun r =>
    binaryNongatewayReactionEquivFin hn gateway
      ⟨r.val, mem_traceNongatewayReactions_ne_gateway
        gateway code.val r.property⟩

theorem card_canonicalReversibleTraceRequiredChannels {n s : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n) (code : ReversibleTraceCode n s) :
    (canonicalReversibleTraceRequiredChannels hn gateway code).card = s - 1 := by
  rw [canonicalReversibleTraceRequiredChannels,
    Finset.card_image_of_injective]
  · simpa using card_traceNongatewayReactions gateway code
  · intro left right h
    apply Subtype.ext
    exact congrArg (fun z : {r : Reaction n // r ≠ gateway} => z.val)
      ((binaryNongatewayReactionEquivFin hn gateway).injective h)

noncomputable def canonicalReversibleFirstHitRequiredChannels {n s : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n) (code : ReversibleFirstHitCode n s) :
    Finset (Fin (sourceReactionCount n - 1)) :=
  canonicalReversibleTraceRequiredChannels hn gateway code.1

theorem card_canonicalReversibleFirstHitRequiredChannels {n s : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n) (code : ReversibleFirstHitCode n s) :
    (canonicalReversibleFirstHitRequiredChannels hn gateway code).card = s - 1 :=
  card_canonicalReversibleTraceRequiredChannels hn gateway code.1

/-- The concrete source reaction set represented by a displayed gateway and
its fixed-size fibre of nongateway catalogue indices. -/
noncomputable def gatewayConditionedReactionSet {n degree : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1)) :
    Finset (Reaction n) :=
  insert gateway <| fibre.val.image fun index =>
    ((binaryNongatewayReactionEquivFin hn gateway).symm index).val

theorem card_gatewayConditionedReactionSet {n degree : Nat}
    (hn : 2 ≤ n) (gateway : Reaction n)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    (hdegree : 1 ≤ degree) :
    (gatewayConditionedReactionSet hn gateway fibre).card = degree := by
  let decode : Fin (sourceReactionCount n - 1) → Reaction n := fun index =>
    ((binaryNongatewayReactionEquivFin hn gateway).symm index).val
  have hdecode : Function.Injective decode := by
    intro left right heq
    apply (binaryNongatewayReactionEquivFin hn gateway).symm.injective
    exact Subtype.ext heq
  have hgateway : gateway ∉ fibre.val.image decode := by
    intro h
    simp only [Finset.mem_image] at h
    obtain ⟨index, _hindex, heq⟩ := h
    exact ((binaryNongatewayReactionEquivFin hn gateway).symm index).property
      heq
  rw [gatewayConditionedReactionSet, show (fun index =>
    ((binaryNongatewayReactionEquivFin hn gateway).symm index).val) =
      decode from rfl, Finset.card_insert_of_notMem hgateway,
    Finset.card_image_of_injective _ hdecode]
  have hfibreCard := (Finset.mem_powersetCard.mp fibre.property).2
  omega

/-- If a legal reversible trace uses only reactions in a conditioned source
fibre, all of its canonical nongateway requirements occur in that fibre. -/
theorem canonicalReversibleTraceRequiredChannels_subset_fibre
    {n degree s : Nat} (hn : 2 ≤ n) (gateway : Reaction n)
    (code : ReversibleTraceCode n s)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    (htrace : code.val.toFinset ⊆
      gatewayConditionedReactionSet hn gateway fibre) :
    canonicalReversibleTraceRequiredChannels hn gateway code ⊆ fibre.val := by
  intro index hindex
  rw [canonicalReversibleTraceRequiredChannels] at hindex
  simp only [Finset.mem_image] at hindex
  obtain ⟨reaction, hreaction, rfl⟩ := hindex
  let nongateway : {r : Reaction n // r ≠ gateway} :=
    ⟨reaction.val, mem_traceNongatewayReactions_ne_gateway
      gateway code.val reaction.property⟩
  change binaryNongatewayReactionEquivFin hn gateway nongateway ∈ fibre.val
  have hsource := htrace
    (traceNongatewayReactions_subset gateway code.val reaction.property)
  rw [gatewayConditionedReactionSet, Finset.mem_insert] at hsource
  rcases hsource with hgateway | himage
  · exact False.elim (nongateway.property hgateway)
  · simp only [Finset.mem_image] at himage
    obtain ⟨catalogueIndex, hcatalogueIndex, heq⟩ := himage
    have hencoded :
        binaryNongatewayReactionEquivFin hn gateway nongateway = catalogueIndex := by
      apply (binaryNongatewayReactionEquivFin hn gateway).symm.injective
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      exact heq.symm
    simpa [hencoded] using hcatalogueIndex

theorem canonicalReversibleFirstHitRequiredChannels_subset_fibre
    {n degree s : Nat} (hn : 2 ≤ n) (gateway : Reaction n)
    (code : ReversibleFirstHitCode n s)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    (htrace : code.1.val.toFinset ⊆
      gatewayConditionedReactionSet hn gateway fibre) :
    canonicalReversibleFirstHitRequiredChannels hn gateway code ⊆ fibre.val :=
  canonicalReversibleTraceRequiredChannels_subset_fibre
    hn gateway code.1 fibre htrace

/-- The two possible newly exposed molecules at the last step of a nonempty
trace.  If the product was already available, cleavage can expose the two
factors; otherwise an enabled last reaction can only newly expose the product. -/
noncomputable def reversibleFirstHitOutput {n s : Nat} (hs : 1 ≤ s)
    (code : ReversibleFirstHitCode n s) : Fin (sourceMoleculeCount n) :=
  let trace := code.1.val
  let r := trace.getLast (by
    have hlength := (mem_reversibleTraceFinset_length_nodup code.1.property).1
    intro hnil
    dsimp only [trace] at hnil
    have hzero : code.1.val.length = 0 := by simp [hnil]
    omega)
  let pref := trace.dropLast
  let x := if reactionProduct r ∈
      reversibleTraceAvailable (binaryFood n 2) pref then
      if code.2.val = 0 then reactionLeft r else reactionRight r
    else reactionProduct r
  binaryMoleculeEquivFin n x

/-- A supported nonempty reversible trace is counted by its canonical
first-hit certificate layer. -/
theorem reversibleFirstHit_mem_canonicalCertificateLayer
    {n degree s : Nat} (hn : 2 ≤ n) (hs : 1 ≤ s)
    (gateway : Reaction n) (code : ReversibleFirstHitCode n s)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    (htrace : code.1.val.toFinset ⊆
      gatewayConditionedReactionSet hn gateway fibre) :
    (reversibleFirstHitOutput hs code, fibre) ∈
      reversibleFirstHitCertificateLayer n (sourceMoleculeCount n)
        (sourceReactionCount n) degree s
        (reversibleFirstHitOutput hs)
        (canonicalReversibleFirstHitRequiredChannels hn gateway) := by
  simp only [reversibleFirstHitCertificateLayer, certificateUnion,
    Finset.mem_biUnion]
  refine ⟨code, Finset.mem_univ code, ?_⟩
  simp only [certificateFibre, Finset.mem_image]
  refine ⟨fibre, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    fixedSizeFibreContains]
  exact canonicalReversibleFirstHitRequiredChannels_subset_fibre
    hn gateway code fibre htrace

/-- A supported length-`n` trace is counted by the canonical survival event. -/
theorem reversibleTrace_mem_canonicalSurvivalCertificateEvent
    {n degree : Nat} (hn : 2 ≤ n) (gateway : Reaction n)
    (code : ReversibleTraceCode n n)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    (htrace : code.val.toFinset ⊆
      gatewayConditionedReactionSet hn gateway fibre) :
    fibre ∈ reversibleSurvivalCertificateEvent n (sourceReactionCount n)
      degree (canonicalReversibleTraceRequiredChannels hn gateway) := by
  simp only [reversibleSurvivalCertificateEvent, Finset.mem_biUnion]
  refine ⟨code, Finset.mem_univ code, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    fixedSizeFibreContains]
  exact canonicalReversibleTraceRequiredChannels_subset_fibre
    hn gateway code fibre htrace

end PowerLawSmallRAF

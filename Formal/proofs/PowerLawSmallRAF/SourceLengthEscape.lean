import proofs.PowerLawSmallRAF.FiniteSeedSourceTransport
import proofs.HordijkSteelThreshold.ReversibleEscape

namespace PowerLawSmallRAF
open Classical RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

/-- Actual reversible source closure escapes length K exactly when its
restriction to channels with product length at most 2K does. -/
theorem source_length_escape_iff_restriction (n K : Nat)
    (hK : 2 ≤ K) (hcap : 2*K ≤ n) (H : Finset (Reaction n)) :
    (∃ x ∈ temporaryReactionClosure 2 H, K < molLength x) ↔
    (∃ x ∈ temporaryReactionClosure 2 (sourceSeedRestriction n (2*K) H),
      K < molLength x) := by
  constructor
  · rintro ⟨x,hx,hlen⟩
    have hx' : x ∈ temporaryReactionClosure 2
        (restrictedSplitReactions n (sourceSeedField n H)) := by
      rwa [restrictedSplitReactions_sourceSeedField]
    have hg := finiteReversibleGenerated_to_infinite
      (literalClosure_to_finiteReversible (sourceSeedField n H) x hx')
    obtain ⟨w,hw,hg⟩ := (reversible_escape_iff_cap hK (sourceSeedField n H)).mp
      ⟨moleculeWord x, by simpa only [moleculeWord_length] using hlen, hg⟩
    have ht := finiteReversibleGenerated_mono_cap hcap (finiteReversibleGenerated_capped hg)
    obtain ⟨y,hy,he⟩ := finiteReversible_to_literalClosure ht
    rw [restrictedSplitReactions_capped_sourceSeedField] at hy
    exact ⟨y,hy,by simpa only [← he,moleculeWord_length] using hw⟩
  · rintro ⟨x,hx,hlen⟩
    exact ⟨x,temporaryReactionClosure_mono (Finset.filter_subset _ _) hx,hlen⟩

/-- A RAF in a nonescaping full source environment supplies an incidence
between a bounded-length catalyst and a bounded-product-length channel.
Both catalogues are fixed before sampling; no selected-owner independence is used. -/
theorem source_nonescaping_RAF_has_bounded_incidence (n K : Nat)
    (config : SourceMoleculeFibreConfig n) (S : Finset (Reaction n))
    (hraf : IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S)
    (hbound : ∀ x ∈ temporaryReactionClosure 2 (Finset.univ.biUnion config),
      molLength x ≤ K) :
    ∃ x : Molecule n, ∃ r : Reaction n,
      molLength x ≤ K ∧ reactionProductLength r ≤ K ∧ r ∈ config x := by
  have hSH : S ⊆ Finset.univ.biUnion config := by
    intro r hr
    obtain ⟨x,k,hx,hcat⟩ := hraf.2.2 r hr
    exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hcat⟩
  obtain ⟨r,hr⟩ := hraf.1
  obtain ⟨x,k,hx,hcat⟩ := hraf.2.2 r hr
  have hxS := (mem_temporaryReactionClosure S x).mpr ⟨k,hx⟩
  have hxH := temporaryReactionClosure_mono hSH hxS
  obtain ⟨j,hgen⟩ := hraf.2.1 r hr
  have hp : reactionProduct r ∈ revClosureAt (binaryPolymerCRS n 2) S j := by
    apply hgen
    simp [binaryPolymerCRS]
  have hpS := (mem_temporaryReactionClosure S (reactionProduct r)).mpr ⟨j,hp⟩
  have hpH := temporaryReactionClosure_mono hSH hpS
  have hpLen : reactionProductLength r ≤ K := by
    simpa only [molLength_reactionProduct] using hbound (reactionProduct r) hpH
  exact ⟨x,r,hbound x hxH,hpLen,hcat⟩

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.SourceFiniteCapLimit
import proofs.PowerLawSmallRAF.SourceEscapeProbability

namespace PowerLawSmallRAF
open Classical Filter Topology MeasureTheory HordijkSteelThreshold RAF.Polymer RAF.Concrete
noncomputable section

theorem source_escape_iff_cap_projection (n K : Nat) (hK : 2 ≤ K)
    (hcap : 2*K ≤ n) (H : Finset (Reaction n)) :
    (∃ x ∈ temporaryReactionClosure 2 H, K < molLength x) ↔
    (∃ x ∈ temporaryReactionClosure 2 (sourceSeedProjection n (2*K) hcap H),
      K < molLength x) := by
  constructor
  · rintro ⟨x,hx,hlen⟩
    have hx' : x ∈ temporaryReactionClosure 2
        (restrictedSplitReactions n (sourceSeedField n H)) := by
      rwa [restrictedSplitReactions_sourceSeedField]
    have hg := finiteReversibleGenerated_to_infinite
      (literalClosure_to_finiteReversible (sourceSeedField n H) x hx')
    obtain ⟨w,hw,hg⟩ := (reversible_escape_iff_cap hK (sourceSeedField n H)).mp
      ⟨moleculeWord x,by simpa only [moleculeWord_length] using hlen,hg⟩
    obtain ⟨y,hy,he⟩ := finiteReversible_to_literalClosure hg
    rw [restrictedSplitReactions_sourceSeedProjection n (2*K) hcap H] at hy
    exact ⟨y,hy,by simpa only [← he,moleculeWord_length] using hw⟩
  · rintro ⟨x,hx,hlen⟩
    rw [← restrictedSplitReactions_sourceSeedProjection n (2*K) hcap H] at hx
    have hg := finiteReversibleGenerated_mono_cap hcap
      (literalClosure_to_finiteReversible (sourceSeedField n H) x hx)
    obtain ⟨y,hy,he⟩ := finiteReversible_to_literalClosure hg
    rw [restrictedSplitReactions_sourceSeedField] at hy
    refine ⟨y,hy,?_⟩
    have hl := congrArg List.length he
    simp only [moleculeWord_length] at hl
    omega

/-- Fixed-length escape probability in the actual source converges to its
finite iid counterpart. The cap is fixed before taking n to infinity. -/
theorem sourceEscapeProbability_tendsto (K : Nat) :
    Tendsto (fun n : Nat => sourceEscapeProbability (2-2/(n : ℝ)) n (K+2))
      atTop (𝓝 ((staticReactionMeasure (2*(K+2)) sourceCriticalOpenness)
        (staticEscapeEvent 2 K)).toReal) := by
  let E : Finset (Reaction (2*(K+2))) → Prop := fun H =>
    ∃ x ∈ temporaryReactionClosure 2 H, K+2 < molLength x
  have ht := sourceFiniteCap_event_tendsto (2*(K+2)) E
  have he : {ω | E (staticOpenReactions ω)} = staticEscapeEvent 2 K := by
    ext ω
    simp only [E,staticEscapeEvent,moleculeWord_length,Set.mem_setOf_eq]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2*(K+2))] with n hn
  unfold sourceEscapeProbability
  apply Finset.sum_congr rfl
  intro config _
  have hiff : E (sourceFiniteCapOpen (2*(K+2)) n config) ↔
      ∃ x ∈ temporaryReactionClosure 2 (Finset.univ.biUnion config), K+2 < molLength x := by
    rw [sourceFiniteCapOpen_eq_projection _ _ hn]
    exact (source_escape_iff_cap_projection n (K+2) (by omega) hn _).symm
  by_cases h : E (sourceFiniteCapOpen (2*(K+2)) n config)
  · rw [if_pos h,if_pos (hiff.mp h)]
  · rw [if_neg h,if_neg (fun hh => h (hiff.mpr hh))]

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.ReversibleProductiveTraces
import proofs.HordijkSteelThreshold.MarkedCoreAdapter

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- All enumerated traces of admissible length that use only reactions in `S`. -/
def reversibleRestrictedTraceUniverse {n : Nat}
    (initial : Finset (Molecule n)) (S : Finset (Reaction n)) :
    Finset (List (Reaction n)) :=
  (Finset.range (S.card + 1)).biUnion fun s =>
    (reversibleTraceFinset initial s).filter fun trace => trace.toFinset ⊆ S

theorem nil_mem_reversibleRestrictedTraceUniverse {n : Nat}
    (initial : Finset (Molecule n)) (S : Finset (Reaction n)) :
    [] ∈ reversibleRestrictedTraceUniverse initial S := by
  simp only [reversibleRestrictedTraceUniverse, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_filter]
  exact ⟨0, Nat.zero_lt_succ _, by simp [reversibleTraceFinset], by simp⟩

theorem mem_reversibleRestrictedTraceUniverse_iff {n : Nat}
    {initial : Finset (Molecule n)} {S : Finset (Reaction n)}
    {trace : List (Reaction n)} :
    trace ∈ reversibleRestrictedTraceUniverse initial S ↔
      trace.length ≤ S.card ∧
      trace ∈ reversibleTraceFinset initial trace.length ∧
      trace.toFinset ⊆ S := by
  simp only [reversibleRestrictedTraceUniverse, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_filter]
  constructor
  · rintro ⟨s, hs, htrace, hsub⟩
    have hlength := (mem_reversibleTraceFinset_length_nodup htrace).1
    subst s
    exact ⟨by omega, htrace, hsub⟩
  · rintro ⟨hlength, htrace, hsub⟩
    exact ⟨trace.length, by omega, htrace, hsub⟩

theorem reversibleReactionStep_subset {n : Nat}
    (available : Finset (Molecule n)) (r : Reaction n) :
    available ⊆ reversibleReactionStep available r := by
  exact Finset.subset_union_left

theorem reversibleTraceAvailable_prefix_subset {n : Nat}
    (initial : Finset (Molecule n)) (pref suffix : List (Reaction n)) :
    reversibleTraceAvailable initial pref ⊆
      reversibleTraceAvailable initial (pref ++ suffix) := by
  induction suffix generalizing pref with
  | nil => simp
  | cons r suffix ih =>
      rw [show pref ++ r :: suffix = (pref ++ [r]) ++ suffix by simp]
      apply (reversibleReactionStep_subset
        (reversibleTraceAvailable initial pref) r).trans
      simpa [reversibleTraceAvailable] using ih (pref ++ [r])

theorem reaction_support_subset_traceAvailable_of_mem {n : Nat}
    (initial : Finset (Molecule n)) {trace : List (Reaction n)}
    {r : Reaction n} (hr : r ∈ trace) :
    ({reactionLeft r, reactionRight r, reactionProduct r} :
      Finset (Molecule n)) ⊆ reversibleTraceAvailable initial trace := by
  obtain ⟨pref, suffix, rfl⟩ := List.mem_iff_append.mp hr
  rw [show pref ++ r :: suffix = (pref ++ [r]) ++ suffix by simp]
  apply Finset.Subset.trans ?_
    (reversibleTraceAvailable_prefix_subset initial (pref ++ [r]) suffix)
  intro x hx
  simp only [reversibleTraceAvailable, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  exact Finset.mem_union_right _ hx

theorem extended_trace_mem_reversibleTraceFinset {n : Nat}
    (initial : Finset (Molecule n)) {trace : List (Reaction n)}
    (htrace : trace ∈ reversibleTraceFinset initial trace.length)
    {r : Reaction n} (hr : r ∈ reversibleTraceNext initial trace) :
    trace ++ [r] ∈ reversibleTraceFinset initial (trace.length + 1) := by
  simp only [reversibleTraceFinset, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨trace, htrace, r, hr, rfl⟩

/-- A longest legal trace inside a finite reaction fibre is saturated: every
reaction of the fibre enabled at its terminal available set was already used. -/
theorem exists_saturated_reversible_trace {n : Nat}
    (initial : Finset (Molecule n)) (S : Finset (Reaction n)) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset initial trace.length ∧
      trace.toFinset ⊆ S ∧ trace.length ≤ S.card ∧
      ∀ r ∈ S,
        ((reactionLeft r ∈ reversibleTraceAvailable initial trace ∧
            reactionRight r ∈ reversibleTraceAvailable initial trace) ∨
          reactionProduct r ∈ reversibleTraceAvailable initial trace) →
        r ∈ trace := by
  let candidates := reversibleRestrictedTraceUniverse initial S
  have hnonempty : candidates.Nonempty :=
    ⟨[], nil_mem_reversibleRestrictedTraceUniverse initial S⟩
  obtain ⟨trace, htraceU, hmax⟩ :=
    Finset.exists_max_image candidates List.length hnonempty
  have htrace := mem_reversibleRestrictedTraceUniverse_iff.mp htraceU
  refine ⟨trace, htrace.2.1, htrace.2.2, htrace.1, ?_⟩
  intro r hrS henabled
  by_contra hrnot
  have hrenabled : r ∈ reversiblyEnabledReactionFinset
      (reversibleTraceAvailable initial trace) := by
    simpa [reversiblyEnabledReactionFinset] using henabled
  have hrnext : r ∈ reversibleTraceNext initial trace := by
    exact Finset.mem_filter.mpr ⟨hrenabled, hrnot⟩
  have hextTrace : trace ++ [r] ∈
      reversibleTraceFinset initial ((trace ++ [r]).length) := by
    simpa using extended_trace_mem_reversibleTraceFinset initial htrace.2.1 hrnext
  have hextNodup := (mem_reversibleTraceFinset_length_nodup hextTrace).2
  have hextSub : (trace ++ [r]).toFinset ⊆ S := by
    simpa using Finset.insert_subset hrS htrace.2.2
  have hextLength : (trace ++ [r]).length ≤ S.card := by
    have hcard := Finset.card_le_card hextSub
    rw [List.toFinset_card_of_nodup hextNodup] at hcard
    exact hcard
  have hextU : trace ++ [r] ∈ candidates :=
    mem_reversibleRestrictedTraceUniverse_iff.mpr
      ⟨hextLength, hextTrace, hextSub⟩
  have hle := hmax (trace ++ [r]) hextU
  simp at hle

theorem binary_revClosureStep_subset_traceAvailable_of_saturated {n : Nat}
    (S : Finset (Reaction n)) (trace : List (Reaction n))
    (hsaturated : ∀ r ∈ S,
      ((reactionLeft r ∈ reversibleTraceAvailable (binaryFood n 2) trace ∧
          reactionRight r ∈ reversibleTraceAvailable (binaryFood n 2) trace) ∨
        reactionProduct r ∈ reversibleTraceAvailable (binaryFood n 2) trace) →
      r ∈ trace) :
    revClosureStep (binaryPolymerCRS n 2) S
      (reversibleTraceAvailable (binaryFood n 2) trace) ⊆
        reversibleTraceAvailable (binaryFood n 2) trace := by
  intro x hx
  simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx
  rcases hx with hx | ⟨r, hrS, hx⟩
  · exact hx
  · by_cases hrtrace : r ∈ trace
    · have hsupport := reaction_support_subset_traceAvailable_of_mem
        (binaryFood n 2) hrtrace
      apply hsupport
      by_cases hl : RevEnabledLhs (binaryPolymerCRS n 2)
          (reversibleTraceAvailable (binaryFood n 2) trace) r
      · by_cases hh : RevEnabledRhs (binaryPolymerCRS n 2)
            (reversibleTraceAvailable (binaryFood n 2) trace) r
        · rw [if_pos hl, if_pos hh] at hx
          simpa [binaryPolymerCRS, or_assoc, or_left_comm, or_comm] using hx
        · rw [if_pos hl, if_neg hh] at hx
          have hp : x = reactionProduct r := by
            simpa [binaryPolymerCRS] using hx
          simp [hp]
      · by_cases hh : RevEnabledRhs (binaryPolymerCRS n 2)
            (reversibleTraceAvailable (binaryFood n 2) trace) r
        · rw [if_neg hl, if_pos hh] at hx
          have hf : x = reactionLeft r ∨ x = reactionRight r := by
            simpa [binaryPolymerCRS] using hx
          rcases hf with rfl | rfl <;> simp
        · rw [if_neg hl, if_neg hh] at hx
          simp at hx
    · have hnotenabled : ¬ ((reactionLeft r ∈
          reversibleTraceAvailable (binaryFood n 2) trace ∧
          reactionRight r ∈ reversibleTraceAvailable (binaryFood n 2) trace) ∨
          reactionProduct r ∈ reversibleTraceAvailable (binaryFood n 2) trace) := by
        intro henabled
        exact hrtrace (hsaturated r hrS henabled)
      have hl : ¬ RevEnabledLhs (binaryPolymerCRS n 2)
          (reversibleTraceAvailable (binaryFood n 2) trace) r := by
        intro h
        apply hnotenabled
        left
        constructor
        · exact h (by simp [binaryPolymerCRS])
        · exact h (by simp [binaryPolymerCRS])
      have hh : ¬ RevEnabledRhs (binaryPolymerCRS n 2)
          (reversibleTraceAvailable (binaryFood n 2) trace) r := by
        intro h
        apply hnotenabled
        right
        exact h (by simp [binaryPolymerCRS])
      rw [if_neg hl, if_neg hh] at hx
      simp at hx

theorem revClosureAt_subset_saturated_traceAvailable {n k : Nat}
    (S : Finset (Reaction n)) (trace : List (Reaction n))
    (hsaturated : ∀ r ∈ S,
      ((reactionLeft r ∈ reversibleTraceAvailable (binaryFood n 2) trace ∧
          reactionRight r ∈ reversibleTraceAvailable (binaryFood n 2) trace) ∨
        reactionProduct r ∈ reversibleTraceAvailable (binaryFood n 2) trace) →
      r ∈ trace) :
    revClosureAt (binaryPolymerCRS n 2) S k ⊆
      reversibleTraceAvailable (binaryFood n 2) trace := by
  induction k with
  | zero =>
      simpa [revClosureAt, binaryPolymerCRS] using
        reversibleTraceAvailable_prefix_subset (binaryFood n 2) [] trace
  | succ k ih =>
      exact (HordijkSteelThreshold.revClosureStep_mono
        (binaryPolymerCRS n 2) Finset.Subset.rfl ih).trans
          (binary_revClosureStep_subset_traceAvailable_of_saturated
            S trace hsaturated)

/-- Every molecule reachable in the literal reversible source is present after
some counted distinct enabled trace using only reactions of the supplied fibre. -/
theorem source_reversible_reachability_has_counted_trace {n k : Nat}
    (S : Finset (Reaction n)) {x : Molecule n}
    (hx : x ∈ revClosureAt (binaryPolymerCRS n 2) S k) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) trace.length ∧
      trace.toFinset ⊆ S ∧ trace.length ≤ S.card ∧
      x ∈ reversibleTraceAvailable (binaryFood n 2) trace := by
  obtain ⟨trace, htrace, hsub, hlength, hsaturated⟩ :=
    exists_saturated_reversible_trace (binaryFood n 2) S
  exact ⟨trace, htrace, hsub, hlength,
    revClosureAt_subset_saturated_traceAvailable S trace hsaturated hx⟩

end PowerLawSmallRAF

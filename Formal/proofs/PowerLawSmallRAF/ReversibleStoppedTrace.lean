import proofs.PowerLawSmallRAF.CanonicalReversibleTraceCertificate

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- Every prefix of an enumerated reversible trace is itself enumerated at
its own length. -/
theorem take_mem_reversibleTraceFinset {n s t : Nat}
    {initial : Finset (Molecule n)} {trace : List (Reaction n)}
    (htrace : trace ∈ reversibleTraceFinset initial s) (ht : t ≤ s) :
    trace.take t ∈ reversibleTraceFinset initial t := by
  induction s generalizing trace t with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      simp [reversibleTraceFinset]
  | succ s ih =>
      simp only [reversibleTraceFinset, Finset.mem_biUnion,
        Finset.mem_image] at htrace
      obtain ⟨pref, hpref, r, hr, rfl⟩ := htrace
      have hprefLength := (mem_reversibleTraceFinset_length_nodup hpref).1
      by_cases htop : t = s + 1
      · subst t
        have hpref' : pref ∈
            reversibleTraceFinset initial pref.length := by
          simpa [hprefLength] using hpref
        have hall := extended_trace_mem_reversibleTraceFinset
          initial hpref' hr
        rw [(List.take_eq_self_iff _).2 (by simp [hprefLength])]
        simpa [hprefLength] using hall
      · have hts : t ≤ s := by omega
        have hp := ih hpref hts
        simpa [List.take_append, hprefLength, hts] using hp

theorem toFinset_take_subset {α : Type*} [DecidableEq α]
    (items : List α) (k : Nat) :
    (items.take k).toFinset ⊆ items.toFinset := by
  intro item hitem
  exact List.mem_toFinset.mpr
    (List.mem_of_mem_take (List.mem_toFinset.mp hitem))

theorem dropLast_take_eq_take_pred {α : Type*} (items : List α) {s : Nat}
    (hs : 1 ≤ s) (hsLength : s ≤ items.length) :
    (items.take s).dropLast = items.take (s - 1) := by
  rw [List.dropLast_eq_take, List.length_take, Nat.min_eq_left hsLength,
    List.take_take]
  congr
  omega

/-- A molecule present at the end but absent initially has a first prefix at
which it appears. -/
theorem exists_first_hit_prefix {n : Nat}
    (initial : Finset (Molecule n)) (trace : List (Reaction n))
    {x : Molecule n} (hxInitial : x ∉ initial)
    (hxFinal : x ∈ reversibleTraceAvailable initial trace) :
    ∃ s : Nat, 1 ≤ s ∧ s ≤ trace.length ∧
      x ∈ reversibleTraceAvailable initial (trace.take s) ∧
      x ∉ reversibleTraceAvailable initial (trace.take (s - 1)) := by
  let P : Nat → Prop := fun s =>
    x ∈ reversibleTraceAvailable initial (trace.take s)
  have hexists : ∃ s, P s := by
    refine ⟨trace.length, ?_⟩
    dsimp only [P]
    rw [(List.take_eq_self_iff _).2 (le_refl _)]
    exact hxFinal
  let s := Nat.find hexists
  have hsHit : P s := Nat.find_spec hexists
  have hsPositive : 1 ≤ s := by
    by_contra hs
    have hs0 : s = 0 := by omega
    have hsHitZero : P 0 := by simpa [hs0] using hsHit
    exact hxInitial (by simpa [P, reversibleTraceAvailable] using hsHitZero)
  have hsLength : s ≤ trace.length := by
    apply Nat.find_min' hexists
    dsimp only [P]
    rw [(List.take_eq_self_iff _).2 (le_refl _)]
    exact hxFinal
  have hsPrevious : ¬ P (s - 1) := by
    apply Nat.find_min hexists
    omega
  exact ⟨s, hsPositive, hsLength, hsHit, hsPrevious⟩

/-- At the first appearance of a molecule, the last enabled reversible
reaction exposes it as one of the two canonical outputs. -/
theorem exists_selector_reversibleFirstHitOutput_eq {n s : Nat}
    (hs : 1 ≤ s) (code : ReversibleTraceCode n s) {x : Molecule n}
    (hxHit : x ∈ reversibleTraceAvailable (binaryFood n 2) code.val)
    (hxPrevious : x ∉ reversibleTraceAvailable (binaryFood n 2)
      code.val.dropLast) :
    ∃ selector : Fin 2,
      reversibleFirstHitOutput hs (code, selector) =
        binaryMoleculeEquivFin n x := by
  rcases code with ⟨trace, htrace⟩
  cases s with
  | zero => omega
  | succ k =>
      simp only [reversibleTraceFinset, Finset.mem_biUnion,
        Finset.mem_image] at htrace
      obtain ⟨pref, hpref, r, hr, rfl⟩ := htrace
      have henabled := (Finset.mem_filter.mp hr).1
      simp only [reversiblyEnabledReactionFinset, Finset.mem_filter,
        Finset.mem_univ, true_and] at henabled
      have hxStep : x ∈ reversibleReactionStep
          (reversibleTraceAvailable (binaryFood n 2) pref) r := by
        simpa [reversibleTraceAvailable] using hxHit
      have hxOld : x ∉ reversibleTraceAvailable (binaryFood n 2) pref := by
        simpa using hxPrevious
      simp only [reversibleReactionStep, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hxStep
      rcases hxStep with hxStep | hxStep
      · exact False.elim (hxOld hxStep)
      · by_cases hp : reactionProduct r ∈
            reversibleTraceAvailable (binaryFood n 2) pref
        · rcases hxStep with hleft | hright | hproduct
          · refine ⟨⟨0, by omega⟩, ?_⟩
            subst x
            simp [reversibleFirstHitOutput, hp]
          · refine ⟨⟨1, by omega⟩, ?_⟩
            subst x
            simp [reversibleFirstHitOutput, hp]
          · subst x
            exact False.elim (hxOld hp)
        · have hligation : reactionLeft r ∈
              reversibleTraceAvailable (binaryFood n 2) pref ∧
              reactionRight r ∈
                reversibleTraceAvailable (binaryFood n 2) pref := by
            rcases henabled with hligation | hcleavage
            · exact hligation
            · exact False.elim (hp hcleavage)
          rcases hxStep with hleft | hright | hproduct
          · subst x
            exact False.elim (hxOld hligation.1)
          · subst x
            exact False.elim (hxOld hligation.2)
          · refine ⟨⟨0, by omega⟩, ?_⟩
            subst x
            simp [reversibleFirstHitOutput, hp]

/-- Source reachability outside food is witnessed either by a canonical first
hit in at most `n` steps or by a supported surviving trace of length `n`. -/
theorem source_reversible_reachability_firstHit_or_survival
    {n degree k : Nat} (hn : 2 ≤ n) (gateway : Reaction n)
    (fibre : FixedSizeFibre (sourceReactionCount n - 1) (degree - 1))
    {x : Molecule n} (hxFood : x ∉ binaryFood n 2)
    (hxReachable : x ∈ revClosureAt (binaryPolymerCRS n 2)
      (gatewayConditionedReactionSet hn gateway fibre) k) :
    (∃ (s : Nat) (hs : 1 ≤ s) (_hsn : s ≤ n)
        (code : ReversibleTraceCode n s) (selector : Fin 2),
      reversibleFirstHitOutput hs (code, selector) =
        binaryMoleculeEquivFin n x ∧
      code.val.toFinset ⊆ gatewayConditionedReactionSet hn gateway fibre) ∨
    (∃ code : ReversibleTraceCode n n,
      code.val.toFinset ⊆ gatewayConditionedReactionSet hn gateway fibre) := by
  obtain ⟨trace, htrace, htraceSubset, _htraceLength, hxFinal⟩ :=
    source_reversible_reachability_has_counted_trace
      (gatewayConditionedReactionSet hn gateway fibre) hxReachable
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
    refine ⟨s, hs, hsn, code, selector, ?_, ?_⟩
    · exact houtput
    exact (toFinset_take_subset trace s).trans htraceSubset
  · have hnLength : n ≤ trace.length := by omega
    have hprefix : trace.take n ∈
        reversibleTraceFinset (binaryFood n 2) n :=
      take_mem_reversibleTraceFinset htrace hnLength
    let code : ReversibleTraceCode n n := ⟨trace.take n, hprefix⟩
    exact Or.inr ⟨code, (toFinset_take_subset trace n).trans htraceSubset⟩

end PowerLawSmallRAF

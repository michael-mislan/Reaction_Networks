import proofs.PowerLawSmallRAF.ReversibleExplorationBranching

namespace PowerLawSmallRAF

open RAF.Polymer RAF.Concrete

/-- Available molecules after following a displayed reversible reaction list. -/
def reversibleTraceAvailable {n : Nat} (initial : Finset (Molecule n)) :
    List (Reaction n) → Finset (Molecule n) :=
  List.foldl reversibleReactionStep initial

/-- Enabled channels not already used by a prefix.  Productive traces form a
subfamily; retaining enabled but idle choices only enlarges the count. -/
def reversibleTraceNext {n : Nat} (initial : Finset (Molecule n))
    (trace : List (Reaction n)) : Finset (Reaction n) :=
  (reversiblyEnabledReactionFinset (reversibleTraceAvailable initial trace)).filter
    fun r => r ∉ trace

/-- Recursive finite enumeration of all distinct-channel enabled reversible
traces of exactly the requested length. -/
def reversibleTraceFinset {n : Nat} (initial : Finset (Molecule n)) :
    Nat → Finset (List (Reaction n))
  | 0 => {[]}
  | s + 1 => (reversibleTraceFinset initial s).biUnion fun trace =>
      (reversibleTraceNext initial trace).image fun r => trace ++ [r]

theorem mem_reversibleTraceFinset_length_nodup {n s : Nat}
    {initial : Finset (Molecule n)} {trace : List (Reaction n)}
    (htrace : trace ∈ reversibleTraceFinset initial s) :
    trace.length = s ∧ trace.Nodup := by
  induction s generalizing trace with
  | zero =>
      simp only [reversibleTraceFinset, Finset.mem_singleton] at htrace
      subst trace
      simp
  | succ s ih =>
      simp only [reversibleTraceFinset, Finset.mem_biUnion,
        Finset.mem_image] at htrace
      obtain ⟨pref, hpref, r, hr, rfl⟩ := htrace
      have hp := ih hpref
      have hrnot : r ∉ pref := (Finset.mem_filter.mp hr).2
      constructor
      · simp [hp.1]
      · simpa only [List.concat_eq_append] using hp.2.concat hrnot

theorem card_reversibleTraceAvailable_le {n s : Nat}
    {initial : Finset (Molecule n)} {trace : List (Reaction n)}
    (htrace : trace ∈ reversibleTraceFinset initial s) :
    (reversibleTraceAvailable initial trace).card ≤ initial.card + 2 * s := by
  induction s generalizing trace with
  | zero =>
      simp only [reversibleTraceFinset, Finset.mem_singleton] at htrace
      subst trace
      simp [reversibleTraceAvailable]
  | succ s ih =>
      simp only [reversibleTraceFinset, Finset.mem_biUnion,
        Finset.mem_image] at htrace
      obtain ⟨pref, hpref, r, hr, rfl⟩ := htrace
      have henabled : r ∈ reversiblyEnabledReactionFinset
          (reversibleTraceAvailable initial pref) :=
        (Finset.mem_filter.mp hr).1
      let enabled : ReversiblyEnabledReaction
          (reversibleTraceAvailable initial pref) := ⟨r, by
        simpa only [reversiblyEnabledReactionFinset, Finset.mem_filter,
          Finset.mem_univ, true_and] using henabled⟩
      have hstep := card_reversibleReactionStep_le_add_two
        (reversibleTraceAvailable initial pref) enabled
      have havailable : reversibleTraceAvailable initial (pref ++ [r]) =
          reversibleReactionStep (reversibleTraceAvailable initial pref) r := by
        simp [reversibleTraceAvailable]
      rw [havailable]
      exact hstep.trans (by
        have hp := ih hpref
        omega)

theorem card_reversibleTraceNext_le_sourceBranch {n s : Nat}
    {initial : Finset (Molecule n)} (hinitial : initial.card ≤ 6)
    {trace : List (Reaction n)} (htrace : trace ∈ reversibleTraceFinset initial s)
    (hsn : s ≤ n) :
    (reversibleTraceNext initial trace).card ≤ sourceReversibleBranchCount n := by
  calc
    (reversibleTraceNext initial trace).card ≤
        (reversiblyEnabledReactionFinset
          (reversibleTraceAvailable initial trace)).card :=
      Finset.card_filter_le _ _
    _ ≤ (reversibleTraceAvailable initial trace).card ^ 2 +
        (reversibleTraceAvailable initial trace).card * n :=
      card_reversiblyEnabledReactionFinset_le _
    _ ≤ sourceReversibleBranchCount n := by
      have hcard : (reversibleTraceAvailable initial trace).card ≤ 6 + 2 * s :=
        (card_reversibleTraceAvailable_le htrace).trans (by omega)
      calc
        (reversibleTraceAvailable initial trace).card ^ 2 +
            (reversibleTraceAvailable initial trace).card * n =
            (reversibleTraceAvailable initial trace).card *
              ((reversibleTraceAvailable initial trace).card + n) := by ring
        _ ≤ (6 + 2 * n) * (6 + 3 * n) := by
          apply Nat.mul_le_mul
          · omega
          · omega
        _ = sourceReversibleBranchCount n := rfl

theorem card_reversibleTraceFinset_le_pow {n s : Nat}
    {initial : Finset (Molecule n)} (hinitial : initial.card ≤ 6)
    (hsn : s ≤ n) :
    (reversibleTraceFinset initial s).card ≤ sourceReversibleBranchCount n ^ s := by
  induction s with
  | zero => simp [reversibleTraceFinset]
  | succ s ih =>
      have hsn' : s ≤ n := by omega
      calc
        (reversibleTraceFinset initial (s + 1)).card ≤
            ∑ trace ∈ reversibleTraceFinset initial s,
              ((reversibleTraceNext initial trace).image
                fun r => trace ++ [r]).card := by
          exact Finset.card_biUnion_le
        _ ≤ ∑ _trace ∈ reversibleTraceFinset initial s,
              sourceReversibleBranchCount n := by
          apply Finset.sum_le_sum
          intro trace htrace
          exact (Finset.card_image_le).trans
            (card_reversibleTraceNext_le_sourceBranch hinitial htrace hsn')
        _ = (reversibleTraceFinset initial s).card *
              sourceReversibleBranchCount n := by simp
        _ ≤ sourceReversibleBranchCount n ^ s *
              sourceReversibleBranchCount n := by
          exact Nat.mul_le_mul_right _ (ih hsn')
        _ = sourceReversibleBranchCount n ^ (s + 1) := by
          rw [pow_succ]

/-- Branching envelope valid for traces of arbitrary length `m`; unlike
`sourceReversibleBranchCount`, it does not assume `m ≤ n`. -/
def sourceReversibleBranchCountAt (n m : Nat) : Nat :=
  (6 + 2 * m) * (6 + 2 * m + n)

theorem card_reversibleTraceNext_le_sourceBranchAt {n m s : Nat}
    {initial : Finset (Molecule n)} (hinitial : initial.card ≤ 6)
    {trace : List (Reaction n)} (htrace : trace ∈ reversibleTraceFinset initial s)
    (hsm : s ≤ m) :
    (reversibleTraceNext initial trace).card ≤
      sourceReversibleBranchCountAt n m := by
  calc
    (reversibleTraceNext initial trace).card ≤
        (reversiblyEnabledReactionFinset
          (reversibleTraceAvailable initial trace)).card :=
      Finset.card_filter_le _ _
    _ ≤ (reversibleTraceAvailable initial trace).card ^ 2 +
        (reversibleTraceAvailable initial trace).card * n :=
      card_reversiblyEnabledReactionFinset_le _
    _ ≤ sourceReversibleBranchCountAt n m := by
      have hcard : (reversibleTraceAvailable initial trace).card ≤ 6 + 2 * m :=
        (card_reversibleTraceAvailable_le htrace).trans (by omega)
      rw [show (reversibleTraceAvailable initial trace).card ^ 2 +
          (reversibleTraceAvailable initial trace).card * n =
          (reversibleTraceAvailable initial trace).card *
            ((reversibleTraceAvailable initial trace).card + n) by ring]
      dsimp [sourceReversibleBranchCountAt]
      exact Nat.mul_le_mul hcard (Nat.add_le_add_right hcard n)

/-- All-length reversible trace count.  Food-generated supports of
exponential size can therefore be counted without the earlier `s ≤ n`
restriction. -/
theorem card_reversibleTraceFinset_le_pow_at {n m s : Nat}
    {initial : Finset (Molecule n)} (hinitial : initial.card ≤ 6)
    (hsm : s ≤ m) :
    (reversibleTraceFinset initial s).card ≤
      sourceReversibleBranchCountAt n m ^ s := by
  induction s with
  | zero => simp [reversibleTraceFinset]
  | succ s ih =>
      have hsm' : s ≤ m := by omega
      calc
        (reversibleTraceFinset initial (s + 1)).card ≤
            ∑ trace ∈ reversibleTraceFinset initial s,
              ((reversibleTraceNext initial trace).image
                fun r => trace ++ [r]).card := Finset.card_biUnion_le
        _ ≤ ∑ _trace ∈ reversibleTraceFinset initial s,
              sourceReversibleBranchCountAt n m := by
          apply Finset.sum_le_sum
          intro trace htrace
          exact (Finset.card_image_le).trans
            (card_reversibleTraceNext_le_sourceBranchAt
              hinitial htrace hsm')
        _ = (reversibleTraceFinset initial s).card *
              sourceReversibleBranchCountAt n m := by simp
        _ ≤ sourceReversibleBranchCountAt n m ^ s *
              sourceReversibleBranchCountAt n m :=
          Nat.mul_le_mul_right _ (ih hsm')
        _ = sourceReversibleBranchCountAt n m ^ (s + 1) := by
          rw [pow_succ]

end PowerLawSmallRAF

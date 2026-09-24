import proofs.PowerLawSmallRAF.ReversibleTraceCertificates

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- A food-generated source support admits a legal distinct trace using every
reaction exactly once.  This upgrades the earlier saturated-trace bridge from
reachability to support enumeration. -/
theorem source_revFoodGenerated_has_full_trace
    {n : Nat} (S : Finset (Reaction n))
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) S.card ∧
      trace.toFinset = S := by
  obtain ⟨trace, htrace, hsub, hlength, hsaturated⟩ :=
    exists_saturated_reversible_trace (binaryFood n 2) S
  have hSsub : S ⊆ trace.toFinset := by
    intro r hr
    obtain ⟨stage, hendpoints⟩ := hfg r hr
    apply List.mem_toFinset.mpr
    apply hsaturated r hr
    left
    constructor
    · apply revClosureAt_subset_saturated_traceAvailable S trace hsaturated
      apply hendpoints
      simp [binaryPolymerCRS]
    · apply revClosureAt_subset_saturated_traceAvailable S trace hsaturated
      apply hendpoints
      simp [binaryPolymerCRS]
  have heq : trace.toFinset = S := Finset.Subset.antisymm hsub hSsub
  have hnodup := (mem_reversibleTraceFinset_length_nodup htrace).2
  have hlen : trace.length = S.card := by
    rw [← List.toFinset_card_of_nodup hnodup, heq]
  exact ⟨trace, by simpa only [hlen] using htrace, heq⟩

noncomputable def sourceFoodGeneratedSupports (n r : Nat) :
    Finset (Finset (Reaction n)) :=
  by
    classical
    exact Finset.univ.filter fun S =>
      S.card = r ∧ RevFoodGenerated (binaryPolymerCRS n 2) S

/-- Source version of the classical polymer support-counting estimate: through
`n` reactions, food-generated supports inject into the counted reversible
trace grammar. -/
theorem card_sourceFoodGeneratedSupports_le
    {n r : Nat} (hrn : r ≤ n) :
    (sourceFoodGeneratedSupports n r).card ≤
      sourceReversibleBranchCount n ^ r := by
  classical
  let supportType := {S : Finset (Reaction n) //
    S ∈ sourceFoodGeneratedSupports n r}
  let traceType := {trace : List (Reaction n) //
    trace ∈ reversibleTraceFinset (binaryFood n 2) r}
  have hwitness : ∀ S : supportType, ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) r ∧
      trace.toFinset = S.1 := by
    intro S
    have hS := (Finset.mem_filter.mp S.2).2
    obtain ⟨trace, htrace, heq⟩ :=
      source_revFoodGenerated_has_full_trace S.1 hS.2
    exact ⟨trace, by simpa only [hS.1] using htrace, heq⟩
  let chosen : supportType → List (Reaction n) := fun S =>
    Classical.choose (hwitness S)
  have hchosenMem : ∀ S, chosen S ∈
      reversibleTraceFinset (binaryFood n 2) r := fun S =>
    (Classical.choose_spec (hwitness S)).1
  have hchosenEq : ∀ S, (chosen S).toFinset = S.1 := fun S =>
    (Classical.choose_spec (hwitness S)).2
  let f : supportType → traceType := fun S => ⟨chosen S, hchosenMem S⟩
  have hinj : Function.Injective f := by
    intro S T hST
    apply Subtype.ext
    have hlist : chosen S = chosen T := congrArg Subtype.val hST
    rw [← hchosenEq S, ← hchosenEq T, hlist]
  have hcard : Fintype.card supportType ≤ Fintype.card traceType :=
    Fintype.card_le_of_injective f hinj
  change (sourceFoodGeneratedSupports n r).card ≤ _
  rw [show Fintype.card supportType =
      (sourceFoodGeneratedSupports n r).card by
    simp [supportType]] at hcard
  rw [show Fintype.card traceType =
      (reversibleTraceFinset (binaryFood n 2) r).card by
    simp [traceType]] at hcard
  exact hcard.trans
    (card_reversibleTraceFinset_le_pow (card_binaryFood_two_le_six n) hrn)

/-- Food-generated supports of arbitrary size admit the all-length trace
envelope.  This is the support-entropy input needed for exponential minimum
RAF bounds. -/
theorem card_sourceFoodGeneratedSupports_le_at (n r : Nat) :
    (sourceFoodGeneratedSupports n r).card ≤
      sourceReversibleBranchCountAt n r ^ r := by
  classical
  let supportType := {S : Finset (Reaction n) //
    S ∈ sourceFoodGeneratedSupports n r}
  let traceType := {trace : List (Reaction n) //
    trace ∈ reversibleTraceFinset (binaryFood n 2) r}
  have hwitness : ∀ S : supportType, ∃ trace : List (Reaction n),
      trace ∈ reversibleTraceFinset (binaryFood n 2) r ∧
      trace.toFinset = S.1 := by
    intro S
    have hS := (Finset.mem_filter.mp S.2).2
    obtain ⟨trace, htrace, heq⟩ :=
      source_revFoodGenerated_has_full_trace S.1 hS.2
    exact ⟨trace, by simpa only [hS.1] using htrace, heq⟩
  let chosen : supportType → List (Reaction n) := fun S =>
    Classical.choose (hwitness S)
  have hchosenMem : ∀ S, chosen S ∈
      reversibleTraceFinset (binaryFood n 2) r := fun S =>
    (Classical.choose_spec (hwitness S)).1
  have hchosenEq : ∀ S, (chosen S).toFinset = S.1 := fun S =>
    (Classical.choose_spec (hwitness S)).2
  let f : supportType → traceType := fun S => ⟨chosen S, hchosenMem S⟩
  have hinj : Function.Injective f := by
    intro S T hST
    apply Subtype.ext
    have hlist : chosen S = chosen T := congrArg Subtype.val hST
    rw [← hchosenEq S, ← hchosenEq T, hlist]
  have hcard : Fintype.card supportType ≤ Fintype.card traceType :=
    Fintype.card_le_of_injective f hinj
  change (sourceFoodGeneratedSupports n r).card ≤ _
  rw [show Fintype.card supportType =
      (sourceFoodGeneratedSupports n r).card by simp [supportType]] at hcard
  rw [show Fintype.card traceType =
      (reversibleTraceFinset (binaryFood n 2) r).card by simp [traceType]] at hcard
  exact hcard.trans (card_reversibleTraceFinset_le_pow_at
    (card_binaryFood_two_le_six n) (le_refl r))

end PowerLawSmallRAF

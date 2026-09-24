import proofs.PowerLawSmallRAF.FiniteSeedSourceBudget

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

/-- A finite reversible seed followed by one-cut extension keeps all base
and extension catalysts. Both budgets include the fixed seed catalogue. -/
theorem source_finite_seed_growing_nucleus_selection
    {Owner : Type*} [Fintype Owner] [DecidableEq Owner]
    (n N m L : Nat) (hNn : N ≤ n) (hLn : L ≤ n)
    (A : Owner → Finset (Reaction n))
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m →
      FiniteReversibleGenerated N 2 (sourceSeedField n (bernoulliRowsUnion A)) w)
    (hmark : SourceAboveSeedMarked n m L (bernoulliRowsUnion A)) :
    ∃ (S : Finset (Reaction n)) (C : Finset Owner),
      S.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
      C.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) := by
  classical
  obtain ⟨B,C0,_,hB,hC0,hcovered0,hused0,hgen0⟩ :=
    source_finite_seed_owner_selection n N m hNn A hseed
  have hmark' : ∀ w ∈ sourceAboveSeedWords m L, ∃ (hn : w.length ≤ n) (i : ligationCuts w)
      (x : Owner), ligationCutReaction n w hn i ∈ A x := by
    intro w hw
    obtain ⟨hn,i,hi⟩ := hmark w hw
    obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hi
    exact ⟨hn,i,x,hx⟩
  obtain ⟨U,C1,_,hC1,hBU,hcovered1,hused1,hgen⟩ :=
    source_seeded_nucleus_selection_power_budget n m L hLn B hgen0 A hmark'
  refine ⟨B ∪ U,C0 ∪ C1,hBU.trans (Nat.add_le_add_right hB _),
    (Finset.card_union_le _ _).trans (Nat.add_le_add hC0 hC1),?_,?_,hgen⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hb | hu
    · obtain ⟨x,hx,hxr⟩ := hcovered0 r hb
      exact ⟨x,Finset.mem_union_left _ hx,hxr⟩
    · obtain ⟨x,hx,hxr⟩ := hcovered1 r hu
      exact ⟨x,Finset.mem_union_right _ hx,hxr⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with h0 | h1
    · obtain ⟨r,hr,hxr⟩ := hused0 x h0
      exact ⟨r,Finset.mem_union_left _ hr,hxr⟩
    · obtain ⟨r,hr,hxr⟩ := hused1 x h1
      exact ⟨r,Finset.mem_union_right _ hr,hxr⟩

end
end PowerLawSmallRAF

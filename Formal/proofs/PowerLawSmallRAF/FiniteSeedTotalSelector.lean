import proofs.PowerLawSmallRAF.VanishingSeedOwnerSelection
import proofs.PowerLawSmallRAF.VanishingSeedRetainedLaw

namespace PowerLawSmallRAF
open Classical RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

theorem sourceFiniteSeedEvent_words (n N m : Nat) (H : Finset (Reaction n))
    (hs : sourceFiniteSeedEvent n N m H) :
    ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m →
      FiniteReversibleGenerated N 2 (sourceSeedField n H) w := by
  intro w h0 hm
  exact hs w ((mem_actualBinaryWords w m).mpr
    ⟨List.length_pos_iff.mp (by omega),hm⟩)

def sourceFiniteSeedSelection (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) : Finset (Reaction n) × Finset (SourceLowOwnerGroup n d) :=
  if h : N ≤ n ∧ L ≤ n ∧ sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
      SourceAboveSeedMarked n m L (bernoulliRowsUnion A) then
    let hex := source_finite_seed_growing_nucleus_selection n N m L h.1 h.2.1 A
      (sourceFiniteSeedEvent_words n N m _ h.2.2.1) h.2.2.2
    ⟨Classical.choose hex,Classical.choose (Classical.choose_spec hex)⟩
  else ⟨∅,∅⟩

theorem sourceFiniteSeedSelection_spec (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (hNn : N ≤ n) (hLn : L ≤ n)
    (hs : sourceFiniteSeedEvent n N m (bernoulliRowsUnion A))
    (he : SourceAboveSeedMarked n m L (bernoulliRowsUnion A)) :
    let S := (sourceFiniteSeedSelection n N m L d A).1
    let C := (sourceFiniteSeedSelection n N m L d A).2
    S.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
    C.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
    (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧ (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
    (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) := by
  simp only [sourceFiniteSeedSelection,dif_pos (And.intro hNn (And.intro hLn (And.intro hs he)))]
  exact Classical.choose_spec (Classical.choose_spec
    (source_finite_seed_growing_nucleus_selection n N m L hNn hLn A
      (sourceFiniteSeedEvent_words n N m _ hs) he))

theorem sourceFiniteSeedSelection_budgets (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) :
    (sourceFiniteSeedSelection n N m L d A).1.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
    (sourceFiniteSeedSelection n N m L d A).2.card ≤ Fintype.card (Reaction N)+2^(L+1) := by
  by_cases h : N ≤ n ∧ L ≤ n ∧ sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
      SourceAboveSeedMarked n m L (bernoulliRowsUnion A)
  · have hh := sourceFiniteSeedSelection_spec n N m L d A h.1 h.2.1 h.2.2.1 h.2.2.2
    exact ⟨hh.1,hh.2.1⟩
  · simp [sourceFiniteSeedSelection,h]

def sourceFiniteSeedOwnerWords (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) : Finset LigationWord :=
  (sourceFiniteSeedSelection n N m L d A).2.image (fun x => sourceOwnerWord x.val)

theorem sourceFiniteSeedOwnerWords_card (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) :
    (sourceFiniteSeedOwnerWords n N m L d A).card ≤ Fintype.card (Reaction N)+2^(L+1) :=
  Finset.card_image_le.trans (sourceFiniteSeedSelection_budgets n N m L d A).2

theorem sourceFiniteSeedOwnerWords_admissible (n N m L : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A ≠ 0)
    (hs : ¬ ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val) :
    targetSetAdmissible n (sourceVanishingLowOwnerLength n)
      ((Fintype.card (Reaction N) : ℝ)+2^(L+1)) (sourceFiniteSeedOwnerWords n N m L d A) := by
  refine ⟨by exact_mod_cast sourceFiniteSeedOwnerWords_card n N m L d A,?_⟩
  intro w hW
  by_cases h : N ≤ n ∧ L ≤ n ∧ sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
      SourceAboveSeedMarked n m L (bernoulliRowsUnion A)
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨r,_,hr⟩ := (sourceFiniteSeedSelection_spec n N m L d A h.1 h.2.1 h.2.2.1 h.2.2.2).2.2.2.1 x hx
    refine ⟨sourceVanishingLowUsedOwner_length n _ d A hw hs x ⟨r,hr⟩,?_⟩
    rw [sourceOwnerWord_length]
    exact Nat.succ_le_of_lt x.val.1.isLt
  · simp [sourceFiniteSeedOwnerWords,sourceFiniteSeedSelection,h] at hW

end
end PowerLawSmallRAF

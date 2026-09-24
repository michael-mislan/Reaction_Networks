import proofs.PowerLawSmallRAF.VanishingLowOwnerAdmissibility
import proofs.PowerLawSmallRAF.FiniteSeedNucleusSelection
import proofs.PowerLawSmallRAF.VanishingBandCoupling

namespace PowerLawSmallRAF
open Classical RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

/-- Finite-seed and extension owners form an admissible actual target set.
The fixed seed base is included in both the reaction and owner budgets. -/
theorem sourceVanishingSeedOwnerSelection (n N m L : Nat) (hNn : N ≤ n) (hLn : L ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d)
    (hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A ≠ 0)
    (hs : ¬ ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val)
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m →
      FiniteReversibleGenerated N 2 (sourceSeedField n (bernoulliRowsUnion A)) w)
    (hmark : SourceAboveSeedMarked n m L (bernoulliRowsUnion A)) :
    ∃ (S : Finset (Reaction n)) (C : Finset (SourceLowOwnerGroup n d)),
      S.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
      C.card ≤ Fintype.card (Reaction N)+2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) ∧
      targetSetAdmissible n (sourceVanishingLowOwnerLength n)
        ((Fintype.card (Reaction N) : ℝ)+2^(L+1))
        (C.image (fun x => sourceOwnerWord x.val)) := by
  obtain ⟨S,C,hS,hC,hcover,hused,hgen⟩ :=
    source_finite_seed_growing_nucleus_selection n N m L hNn hLn A hseed hmark
  refine ⟨S,C,hS,hC,hcover,hused,hgen,?_,?_⟩
  · have hc := (Finset.card_image_le (f := fun x : SourceLowOwnerGroup n d => sourceOwnerWord x.val)).trans hC
    exact_mod_cast hc
  · intro w hwW
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hwW
    obtain ⟨r,_,hr⟩ := hused x hx
    refine ⟨sourceVanishingLowUsedOwner_length n _ d A hw hs x ⟨r,hr⟩,?_⟩
    rw [sourceOwnerWord_length]
    exact Nat.succ_le_of_lt x.val.1.isLt

end
end PowerLawSmallRAF

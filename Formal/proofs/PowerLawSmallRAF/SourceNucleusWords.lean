import proofs.PowerLawSmallRAF.SourceOwnerWords
import proofs.PowerLawSmallRAF.SourceNucleusSelection

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

def sourceNonfoodNucleusWords (L : Nat) : Finset LigationWord :=
  (Finset.univ.image (@sourceOwnerWord L)).filter (fun w => 3 ≤ w.length)

theorem mem_sourceNonfoodNucleusWords (L : Nat) (w : LigationWord) :
    w ∈ sourceNonfoodNucleusWords L ↔ 3 ≤ w.length ∧ w.length ≤ L := by
  classical
  constructor
  · intro hw
    obtain ⟨hw,h3⟩ := Finset.mem_filter.mp hw
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨h3,?_⟩
    rw [sourceOwnerWord_length]
    have hx := x.1.isLt
    unfold molLength
    omega
  · rintro ⟨h3,hL⟩
    let x := ligationWordMolecule L w (by omega) hL
    have he : sourceOwnerWord x = w := by
      apply ligationWordCode_injective_of_length
      · rw [sourceOwnerWord_length,ligationWordMolecule_length]
      · rw [sourceOwnerWord_code,ligationWordMolecule_code]
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,he⟩,h3⟩

theorem source_molecule_card_budget (L : Nat) :
    Fintype.card (Molecule L) + 2 = 2^(L+1) := by
  rw [card_molecule_sigma]
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [show L+1+1=(L+1)+1 from rfl,pow_succ]
    omega

theorem sourceNonfoodNucleusWords_card_le (L : Nat) :
    (sourceNonfoodNucleusWords L).card ≤ 2^(L+1) := by
  classical
  calc
    _ ≤ (Finset.univ.image (@sourceOwnerWord L)).card := Finset.card_filter_le _ _
    _ ≤ Fintype.card (Molecule L) := (Finset.card_image_le).trans (by simp)
    _ ≤ _ := by have h := source_molecule_card_budget L; omega

theorem source_nucleus_selection_power_budget {Owner : Type*} [DecidableEq Owner]
    (n L : Nat) (hLn : L ≤ n) (A : Owner → Finset (Reaction n))
    (hmark : ∀ w ∈ sourceNonfoodNucleusWords L,
      ∃ (hn : w.length ≤ n) (i : ligationCuts w) (x : Owner),
        ligationCutReaction n w hn i ∈ A x) :
    ∃ (S : Finset (Reaction n)) (C : Finset Owner),
      S.card ≤ 2^(L+1) ∧ C.card ≤ 2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) := by
  obtain ⟨S,C,hS,hC,hr,hx,hgen⟩ := source_nucleus_bounded_selection n L hLn A
    (sourceNonfoodNucleusWords L) (mem_sourceNonfoodNucleusWords L) hmark
  exact ⟨S,C,hS.trans (sourceNonfoodNucleusWords_card_le L),
    hC.trans (sourceNonfoodNucleusWords_card_le L),hr,hx,hgen⟩

end
end PowerLawSmallRAF

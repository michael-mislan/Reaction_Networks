import proofs.PowerLawSmallRAF.LigationSourceReaction

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section

theorem exists_ligationWord_of_code (l c : Nat) (hc : c < 2^l) :
    ∃ w : LigationWord, w.length = l ∧ ligationWordCode w = c := by
  induction l generalizing c with
  | zero =>
    have hz : c=0 := by simpa using hc
    subst c
    exact ⟨[],rfl,rfl⟩
  | succ l ih =>
    by_cases h : c < 2^l
    · obtain ⟨w,hw,hc⟩ := ih c h
      exact ⟨false::w,by simp [hw],by simp [ligationWordCode,hc]⟩
    · have hlt : c-2^l < 2^l := by rw [pow_succ] at hc; omega
      obtain ⟨w,hw,hcode⟩ := ih (c-2^l) hlt
      refine ⟨true::w,by simp [hw],?_⟩
      simp only [ligationWordCode,ite_true,hw,hcode]
      omega

def sourceOwnerWord {n : Nat} (x : Molecule n) : LigationWord :=
  Classical.choose (exists_ligationWord_of_code (molLength x) x.2.val x.2.isLt)

theorem sourceOwnerWord_length {n : Nat} (x : Molecule n) : (sourceOwnerWord x).length = molLength x :=
  (Classical.choose_spec (exists_ligationWord_of_code (molLength x) x.2.val x.2.isLt)).1

theorem sourceOwnerWord_code {n : Nat} (x : Molecule n) : ligationWordCode (sourceOwnerWord x) = x.2.val :=
  (Classical.choose_spec (exists_ligationWord_of_code (molLength x) x.2.val x.2.isLt)).2

theorem sourceOwnerWord_injective {n : Nat} : Function.Injective (@sourceOwnerWord n) := by
  intro x y h
  apply sourceMolecule_eq_of_length_code
  · rw [← sourceOwnerWord_length x,← sourceOwnerWord_length y,h]
  · rw [← sourceOwnerWord_code x,← sourceOwnerWord_code y,h]

theorem sourceOwnerWord_roundtrip {n : Nat} (x : Molecule n)
    (h0 : 1 ≤ (sourceOwnerWord x).length) (hn : (sourceOwnerWord x).length ≤ n) :
    ligationWordMolecule n (sourceOwnerWord x) h0 hn = x := by
  apply sourceMolecule_eq_of_length_code
  · rw [ligationWordMolecule_length,sourceOwnerWord_length]
  · rw [ligationWordMolecule_code,sourceOwnerWord_code]

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.BoundedGeneratedOwnerRAF
import proofs.PowerLawSmallRAF.ActualBoundedTargetProbability

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

/-- Actual low nucleus plus bounded high-field derivations closes a source
RAF. The conclusion counts the nucleus and every retained target channel. -/
theorem source_twoBand_boundedRAF_assembly (n L : Nat) (hL : 3 ≤ L) (hLn : L ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d)
    (H : Finset (Reaction n)) (config : SourceMoleculeFibreConfig n)
    (hlow : ∀ x : SourceLowOwnerGroup n d, A x ⊆ config x.val)
    (hhigh : ∀ r ∈ H, ∃ x : Molecule n,
      sourceShrinkingLower n ≤ (d x).val ∧ r ∈ config x)
    (hmark : SourceNucleusMarked n L (bernoulliRowsUnion A))
    (hwitness : ∀ w ∈ sourceHighTargetSet n d ∪ sourceLowNucleusOwnerWords n L d A,
      ∃ U : Finset (Reaction n), U ⊆ H ∧ U.card ≤ w.length-1 ∧
        SourceLigationGenerated n ((sourceLowNucleusSelection n L d A).1 ∪ U) w) :
    ∃ T : Finset (Reaction n),
      T.card ≤ 2^(L+1) + ((sourceHighTargetSet n d).card + 2^(L+1))*n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T := by
  classical
  let B := (sourceLowNucleusSelection n L d A).1
  let W := sourceHighTargetSet n d ∪ sourceLowNucleusOwnerWords n L d A
  have hs := sourceLowNucleusSelection_spec n L d A hLn hmark
  have hWlen : ∀ w ∈ W, w.length ≤ n := by
    intro w hw
    rcases Finset.mem_union.mp hw with hh | hl
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hh
      rw [sourceOwnerWord_length]
      have hx := x.1.isLt
      unfold molLength
      omega
    · exact sourceLowNucleusOwnerWords_length_le n L d A w hl
  obtain ⟨U,hUH,hUcard,hBUcard,hgenerated⟩ :=
    bounded_target_witness_union n B H W hWlen hwitness
  let owners := Finset.univ.filter (fun x : Molecule n => sourceOwnerWord x ∈ W)
  have hcover : ∀ r ∈ B ∪ U, ∃ x ∈ owners, r ∈ config x := by
    intro r hr
    rcases Finset.mem_union.mp hr with hb | hu
    · obtain ⟨x,hx,hxr⟩ := hs.2.2.1 r hb
      refine ⟨x.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hlow x hxr⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨x,hx,hxr⟩ := hhigh r (hUH hu)
      refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hxr⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩)
  have howners : ∀ x ∈ owners, ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS n 2) (B ∪ U) k := by
    intro x hx
    obtain ⟨h0,hn,k,hk⟩ := hgenerated (sourceOwnerWord x) (Finset.mem_filter.mp hx).2
    rw [sourceOwnerWord_roundtrip] at hk
    exact ⟨k,hk⟩
  have hnew : ∃ y k, y ∉ (binaryPolymerCRS n 2).food ∧
      y ∈ revClosureAt (binaryPolymerCRS n 2) (B ∪ U) k := by
    have hg : SourceLigationGenerated n B [false,false,false] :=
      hs.2.2.2.2 _ (by decide) (by simpa using hL)
    have hgu := sourceLigationGenerated_mono n B (B ∪ U) (Finset.subset_union_left) _ hg
    obtain ⟨h0,hn,k,hk⟩ := hgu
    refine ⟨_,k,?_,hk⟩
    simp only [binaryPolymerCRS,binaryFood,Finset.mem_filter,Finset.mem_univ,true_and,
      ligationWordMolecule_length,List.length_cons,List.length_nil]
    omega
  obtain ⟨T,_,hTcard,hraf⟩ :=
    exists_source_boundedRAF_of_generated_owners config (B ∪ U) owners hcover howners hnew
  refine ⟨T,hTcard.trans (hBUcard.trans ?_),hraf⟩
  apply Nat.add_le_add hs.1
  apply Nat.mul_le_mul_right
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (sourceLowNucleusOwnerWords_card_le n L d A) _)

end
end PowerLawSmallRAF

import proofs.PowerLawSmallRAF.FiniteSeedTotalSelector
import proofs.PowerLawSmallRAF.SourceTwoBandConstructionEvent

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete
noncomputable section

/-- Retain the whole reversible seed base, then bounded high-field
derivations of all high owners and every selected low owner. -/
theorem source_finiteSeed_boundedRAF_assembly (n N m L : Nat)
    (hNn : N ≤ n) (hL : 3 ≤ L) (hLn : L ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d)
    (H : Finset (Reaction n)) (config : SourceMoleculeFibreConfig n)
    (hlow : ∀ x : SourceLowOwnerGroup n d, A x ⊆ config x.val)
    (hhigh : ∀ r ∈ H, ∃ x : Molecule n, sourceShrinkingLower n ≤ (d x).val ∧ r ∈ config x)
    (hseed : sourceFiniteSeedEvent n N m (bernoulliRowsUnion A))
    (hext : SourceAboveSeedMarked n m L (bernoulliRowsUnion A))
    (hwitness : ∀ w ∈ sourceHighTargetSet n d ∪ sourceFiniteSeedOwnerWords n N m L d A,
      ∃ U : Finset (Reaction n), U ⊆ H ∧ U.card ≤ w.length-1 ∧
        SourceLigationGenerated n ((sourceFiniteSeedSelection n N m L d A).1 ∪ U) w) :
    ∃ T : Finset (Reaction n),
      T.card ≤ (Fintype.card (Reaction N)+2^(L+1)) +
        ((sourceHighTargetSet n d).card + (Fintype.card (Reaction N)+2^(L+1)))*n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T := by
  let B := (sourceFiniteSeedSelection n N m L d A).1
  let W := sourceHighTargetSet n d ∪ sourceFiniteSeedOwnerWords n N m L d A
  have hs := sourceFiniteSeedSelection_spec n N m L d A hNn hLn hseed hext
  have hWlen : ∀ w ∈ W, w.length ≤ n := by
    intro w hw
    rcases Finset.mem_union.mp hw with hh | hl
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hh
      rw [sourceOwnerWord_length]
      exact Nat.succ_le_of_lt x.1.isLt
    · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hl
      rw [sourceOwnerWord_length]
      exact Nat.succ_le_of_lt x.val.1.isLt
  obtain ⟨U,hUH,_,hBUcard,hgenerated⟩ := bounded_target_witness_union n B H W hWlen hwitness
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
  have howners : ∀ x ∈ owners, ∃ k, x ∈ revClosureAt (binaryPolymerCRS n 2) (B ∪ U) k := by
    intro x hx
    obtain ⟨h0,hn,k,hk⟩ := hgenerated (sourceOwnerWord x) (Finset.mem_filter.mp hx).2
    rw [sourceOwnerWord_roundtrip] at hk
    exact ⟨k,hk⟩
  have hnew : ∃ y k, y ∉ (binaryPolymerCRS n 2).food ∧
      y ∈ revClosureAt (binaryPolymerCRS n 2) (B ∪ U) k := by
    have hg : SourceLigationGenerated n B [false,false,false] :=
      hs.2.2.2.2 _ (by decide) (by simpa using hL)
    have hgu := sourceLigationGenerated_mono n B (B ∪ U) Finset.subset_union_left _ hg
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
    (Nat.add_le_add_left (sourceFiniteSeedOwnerWords_card n N m L d A) _)

def sourceFiniteSeedConstructionBudget (N n : Nat) : Nat :=
  (Fintype.card (Reaction N)+2^(targetNucleusLength n+1)) +
    (n^3*2^shrinkingBandWidth n+(Fintype.card (Reaction N)+2^(targetNucleusLength n+1)))*n

def SourceFiniteSeedConstructionGood (n N m : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (H : Finset (Reaction n)) : Prop :=
  sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
  SourceAboveSeedMarked n m (targetNucleusLength n) (bernoulliRowsUnion A) ∧
  targetSetAdmissible n (n-2*shrinkingBandWidth n)
    ((n : ℝ)^3*2^shrinkingBandWidth n) (sourceHighTargetSet n d) ∧
  ¬ SourceBoundedTargetBad n (targetNucleusLength n) (sourceHighTargetSet n d)
    (sourceFiniteSeedSelection n N m (targetNucleusLength n) d A).1 H ∧
  ¬ SourceBoundedTargetBad n (targetNucleusLength n)
    (sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A)
    (sourceFiniteSeedSelection n N m (targetNucleusLength n) d A).1 H

theorem sourceFiniteSeedConstructionGood_implies_boundedRAF (n N m : Nat) (hNn : N ≤ n)
    (hL : 3 ≤ targetNucleusLength n) (hLn : targetNucleusLength n ≤ n)
    (d : SourceDegreeConfig n) (config : SourceMoleculeFibreConfig n)
    (hgood : SourceFiniteSeedConstructionGood n N m d (fun x => config x.val)
      (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val))) :
    ∃ T : Finset (Reaction n), T.card ≤ sourceFiniteSeedConstructionBudget N n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T := by
  let A : RetainedSourceLowRows n d := fun x => config x.val
  let H := bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val)
  have hs := sourceFiniteSeedSelection_spec n N m (targetNucleusLength n) d A hNn hLn hgood.1 hgood.2.1
  have hnucleus (w u : LigationWord) (hu : u ∈ ligationTargetNucleus (targetNucleusLength n) w) :
      SourceLigationGenerated n (sourceFiniteSeedSelection n N m (targetNucleusLength n) d A).1 u := by
    have huf := Finset.mem_filter.mp hu
    have hne := ((mem_ligationSubstrings_iff w u).mp huf.1).2
    exact hs.2.2.2.2 u (by have hh := List.length_pos_iff.mpr hne; omega) huf.2
  have hw : ∀ w ∈ sourceHighTargetSet n d ∪ sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A,
      ∃ U : Finset (Reaction n), U ⊆ H ∧ U.card ≤ w.length-1 ∧
        SourceLigationGenerated n ((sourceFiniteSeedSelection n N m (targetNucleusLength n) d A).1 ∪ U) w := by
    intro w hw
    by_contra hb
    rcases Finset.mem_union.mp hw with hh | hl
    · exact hgood.2.2.2.1 ⟨w,hh,hnucleus w,hb⟩
    · exact hgood.2.2.2.2 ⟨w,hl,hnucleus w,hb⟩
  have hh : ∀ r ∈ H, ∃ x : Molecule n, sourceShrinkingLower n ≤ (d x).val ∧ r ∈ config x := by
    intro r hr
    obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hr
    exact ⟨x.val,le_of_not_gt x.property,hx⟩
  obtain ⟨T,hT,hraf⟩ := source_finiteSeed_boundedRAF_assembly n N m (targetNucleusLength n)
    hNn hL hLn d A H config (fun _ => Finset.Subset.rfl) hh hgood.1 hgood.2.1 hw
  refine ⟨T,hT.trans ?_,hraf⟩
  have hcard : (sourceHighTargetSet n d).card ≤ n^3*2^shrinkingBandWidth n := by
    exact_mod_cast hgood.2.2.1.1
  exact Nat.add_le_add_left (Nat.mul_le_mul_right n (Nat.add_le_add_right hcard _)) _

end
end PowerLawSmallRAF

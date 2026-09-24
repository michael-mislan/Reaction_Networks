import proofs.PowerLawSmallRAF.SourceTwoBandBoundedAssembly

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete
noncomputable section
attribute [local instance] Classical.propDecidable

def SourceBoundedTargetBad (n L : Nat) (W : Finset LigationWord)
    (B H : Finset (Reaction n)) : Prop :=
  ∃ w ∈ W, (∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n B u) ∧
    ¬ (∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
      SourceLigationGenerated n (B ∪ S) w)

def sourceTwoBandConstructionBudget (n : Nat) : Nat :=
  2^(targetNucleusLength n+1) +
    (n^3*2^(shrinkingBandWidth n)+2^(targetNucleusLength n+1))*n

def SourceTwoBandConstructionGood (n : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (H : Finset (Reaction n)) : Prop :=
  SourceNucleusMarked n (targetNucleusLength n) (bernoulliRowsUnion A) ∧
  targetSetAdmissible n (n-2*shrinkingBandWidth n)
    ((n : ℝ)^3*(2 : ℝ)^shrinkingBandWidth n) (sourceHighTargetSet n d) ∧
  ¬ SourceBoundedTargetBad n (targetNucleusLength n) (sourceHighTargetSet n d)
    (sourceLowNucleusSelection n (targetNucleusLength n) d A).1 H ∧
  ¬ SourceBoundedTargetBad n (targetNucleusLength n)
    (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A)
    (sourceLowNucleusSelection n (targetNucleusLength n) d A).1 H

/-- The construction event is expressed only in retained low rows and the
high union, yet implies an actual bounded RAF for the full row assignment. -/
theorem sourceTwoBandConstructionGood_implies_boundedRAF (n : Nat)
    (hL : 3 ≤ targetNucleusLength n) (hLn : targetNucleusLength n ≤ n)
    (d : SourceDegreeConfig n) (config : SourceMoleculeFibreConfig n)
    (hgood : SourceTwoBandConstructionGood n d (fun x => config x.val)
      (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val))) :
    ∃ T : Finset (Reaction n), T.card ≤ sourceTwoBandConstructionBudget n ∧
      IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) T := by
  classical
  let A : RetainedSourceLowRows n d := fun x => config x.val
  let H := bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val)
  have hs := sourceLowNucleusSelection_spec n (targetNucleusLength n) d A hLn hgood.1
  have hnucleus (w u : LigationWord) (hu : u ∈ ligationTargetNucleus (targetNucleusLength n) w) :
      SourceLigationGenerated n (sourceLowNucleusSelection n (targetNucleusLength n) d A).1 u := by
    have huf := Finset.mem_filter.mp hu
    have hne := ((mem_ligationSubstrings_iff w u).mp huf.1).2
    exact hs.2.2.2.2 u (by have hh := List.length_pos_iff.mpr hne; omega) huf.2
  have hw : ∀ w ∈ sourceHighTargetSet n d ∪
      sourceLowNucleusOwnerWords n (targetNucleusLength n) d A,
      ∃ U : Finset (Reaction n), U ⊆ H ∧ U.card ≤ w.length-1 ∧
        SourceLigationGenerated n ((sourceLowNucleusSelection n (targetNucleusLength n) d A).1 ∪ U) w := by
    intro w hw
    by_contra hb
    rcases Finset.mem_union.mp hw with hh | hl
    · exact hgood.2.2.1 ⟨w,hh,hnucleus w,hb⟩
    · exact hgood.2.2.2 ⟨w,hl,hnucleus w,hb⟩
  have hh : ∀ r ∈ H, ∃ x : Molecule n,
      sourceShrinkingLower n ≤ (d x).val ∧ r ∈ config x := by
    intro r hr
    obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hr
    exact ⟨x.val,le_of_not_gt x.property,hx⟩
  obtain ⟨T,hT,hraf⟩ := source_twoBand_boundedRAF_assembly n (targetNucleusLength n)
    hL hLn d A H config (fun _ => Finset.Subset.rfl) hh hgood.1 hw
  refine ⟨T,hT.trans ?_,hraf⟩
  have hcard : (sourceHighTargetSet n d).card ≤ n^3*2^(shrinkingBandWidth n) := by
    exact_mod_cast hgood.2.1.1
  exact Nat.add_le_add_left (Nat.mul_le_mul_right n (Nat.add_le_add_right hcard _)) _

end
end PowerLawSmallRAF

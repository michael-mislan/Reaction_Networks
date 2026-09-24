import proofs.PowerLawSmallRAF.BoundedTargetProbability

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

theorem bounded_target_witness_union (n : Nat) (B H : Finset (Reaction n))
    (W : Finset LigationWord) (hW : ∀ w ∈ W, w.length ≤ n)
    (hw : ∀ w ∈ W, ∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
      SourceLigationGenerated n (B ∪ S) w) :
    ∃ U : Finset (Reaction n), U ⊆ H ∧ U.card ≤ W.card*n ∧
      (B ∪ U).card ≤ B.card+W.card*n ∧
      ∀ w ∈ W, SourceLigationGenerated n (B ∪ U) w := by
  classical
  let S : W → Finset (Reaction n) := fun w => Classical.choose (hw w.val w.property)
  have hs (w : W) : S w ⊆ H ∧ (S w).card ≤ w.val.length-1 ∧
      SourceLigationGenerated n (B ∪ S w) w.val := Classical.choose_spec (hw w.val w.property)
  let U := Finset.univ.biUnion S
  have hU : U.card ≤ W.card*n := by
    calc
      _ ≤ ∑ w : W, (S w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w : W, n := Finset.sum_le_sum (fun w _ =>
        (hs w).2.1.trans ((Nat.sub_le _ _).trans (hW w.val w.property)))
      _ = _ := by simp
  refine ⟨U,?_,hU,(Finset.card_union_le _ _).trans (Nat.add_le_add_left hU _),?_⟩
  · intro r hr
    obtain ⟨w,_,hr⟩ := Finset.mem_biUnion.mp hr
    exact (hs w).1 hr
  · intro w hwW
    let v : W := ⟨w,hwW⟩
    apply sourceLigationGenerated_mono n (B ∪ S v) (B ∪ U) _ w (hs v).2.2
    apply Finset.union_subset_union_right
    intro r hr
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,hr⟩

end
end PowerLawSmallRAF

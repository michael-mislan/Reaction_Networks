import proofs.PowerLawSmallRAF.LigationSourceProjection

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section

theorem sourceLigationGenerated_mono (n : Nat) (S T : Finset (Reaction n))
    (hST : S ⊆ T) (w : LigationWord) (hw : SourceLigationGenerated n S w) :
    SourceLigationGenerated n T w := by
  obtain ⟨h0,hn,k,hk⟩ := hw
  exact ⟨h0,hn,k,revClosureAt_mono_reaction_set _ hST k hk⟩

def BoundedLigationWitness (n : Nat) (B H : Finset (Reaction n)) (w : LigationWord) : Prop :=
  1 ≤ w.length ∧ ∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
    SourceLigationGenerated n (B ∪ S) w

theorem boundedLigationWitness_base (n : Nat) (B H : Finset (Reaction n))
    (w : LigationWord) (hw : SourceLigationGenerated n B w) : BoundedLigationWitness n B H w := by
  obtain ⟨h0,hn,k,hk⟩ := hw
  refine ⟨h0,∅,Finset.empty_subset _,by simp,?_⟩
  simpa only [Finset.union_empty] using (show SourceLigationGenerated n B w from ⟨h0,hn,k,hk⟩)

theorem boundedLigationWitness_cut (n : Nat) (B H : Finset (Reaction n))
    (w : LigationWord) (hn : w.length ≤ n) (i : ligationCuts w)
    (hr : ligationCutReaction n w hn i ∈ H)
    (hp : BoundedLigationWitness n B H (w.take i.val))
    (hs : BoundedLigationWitness n B H (w.drop i.val)) : BoundedLigationWitness n B H w := by
  classical
  obtain ⟨hp0,P,hPH,hPc,hPg⟩ := hp
  obtain ⟨hs0,S,hSH,hSc,hSg⟩ := hs
  let r := ligationCutReaction n w hn i
  let U := insert r (P ∪ S)
  have hi := Finset.mem_Ioo.mp i.property
  refine ⟨by omega,U,?_,?_,?_⟩
  · exact Finset.insert_subset_iff.mpr ⟨hr,Finset.union_subset hPH hSH⟩
  · have hc : U.card ≤ P.card+S.card+1 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) 1)
    have hpt : (w.take i.val).length = i.val := List.length_take_of_le (by omega)
    have hst : (w.drop i.val).length = w.length-i.val := List.length_drop
    omega
  · apply sourceLigationGenerated_of_cut n (B ∪ U) w hn i
    · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    · apply sourceLigationGenerated_mono n (B ∪ P) (B ∪ U) _ _ hPg
      exact Finset.union_subset_union_right (Finset.Subset.trans Finset.subset_union_left (Finset.subset_insert _ _))
    · apply sourceLigationGenerated_mono n (B ∪ S) (B ∪ U) _ _ hSg
      exact Finset.union_subset_union_right (Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert _ _))

/-- Successful raw ligation generation retains at most length-1 additional
actual channels, even when substring occurrences share reactions. -/
theorem ligationRawKnown_bounded_witness (n : Nat) (B H : Finset (Reaction n))
    (words : List LigationWord) (cfg : LigationRawConfiguration words)
    (known : Finset LigationWord) (hsupp : SourceLigationRawSupported n H words cfg)
    (hk : ∀ u ∈ known, BoundedLigationWitness n B H u) :
    ∀ u ∈ ligationRawKnown words cfg known, BoundedLigationWitness n B H u := by
  classical
  induction words generalizing known with
  | nil => exact hk
  | cons w rest ih =>
    change (∀ i : ligationCuts w, cfg.1 i = true →
      ∃ hn : w.length ≤ n, ligationCutReaction n w hn i ∈ H) ∧
      SourceLigationRawSupported n H rest cfg.2 at hsupp
    dsimp only [ligationRawKnown]
    apply ih cfg.2 _ hsupp.2
    by_cases hf : fullLigationRowFails known w cfg.1
    · simpa only [if_pos hf] using hk
    · rw [if_neg hf]
      have hhit := hf
      simp only [fullLigationRowFails] at hhit
      push Not at hhit
      obtain ⟨i,hi,hb⟩ := hhit
      obtain ⟨hn,hr⟩ := hsupp.1 i (Bool.eq_true_of_not_eq_false hb)
      have ha := (Finset.mem_filter.mp hi).2
      have hp := (Finset.mem_filter.mp ha).2.1
      have hs := (Finset.mem_filter.mp ha).2.2
      have hw := boundedLigationWitness_cut n B H w hn i hr (hk _ hp) (hk _ hs)
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hw
      · exact hk u hu

theorem sourceRawTarget_bounded_witness (n L : Nat) (B H : Finset (Reaction n))
    (w : LigationWord) (hn : w.length ≤ n)
    (hk : ∀ u ∈ ligationTargetNucleus L w, SourceLigationGenerated n B u)
    (hw : w ∈ ligationRawKnown (ligationSubstringSchedule w)
      (sourceLigationTargetConfiguration n w hn H) (ligationTargetNucleus L w)) :
    ∃ S : Finset (Reaction n), S ⊆ H ∧ S.card ≤ w.length-1 ∧
      SourceLigationGenerated n (B ∪ S) w := by
  exact (ligationRawKnown_bounded_witness n B H _ _ _
    (sourceLigationRawConfiguration_supported n H H (Finset.Subset.refl _) _
      (ligationSubstringSchedule_source_bounds n w hn))
    (fun u hu => boundedLigationWitness_base n B H u (hk u hu)) w hw).2

end
end PowerLawSmallRAF

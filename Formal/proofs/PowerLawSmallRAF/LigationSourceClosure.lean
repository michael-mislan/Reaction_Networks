import proofs.PowerLawSmallRAF.LigationSourceReaction
import proofs.PowerLawSmallRAF.LigationStaticHistoryLaw
import proofs.PowerLawSmallRAF.SourceOwnerStage

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section
set_option maxHeartbeats 100000

/-- The word is generated from the actual horizon-two food by the given channels. -/
def SourceLigationGenerated (n : Nat) (T : Finset (Reaction n)) (w : LigationWord) : Prop :=
  ∃ (h0 : 1 ≤ w.length) (hn : w.length ≤ n) (k : Nat),
    ligationWordMolecule n w h0 hn ∈ revClosureAt (binaryPolymerCRS n 2) T k

theorem sourceLigationGenerated_of_cut (n : Nat) (T : Finset (Reaction n))
    (w : LigationWord) (hn : w.length ≤ n) (i : ligationCuts w)
    (hr : ligationCutReaction n w hn i ∈ T)
    (hp : SourceLigationGenerated n T (w.take i.val))
    (hs : SourceLigationGenerated n T (w.drop i.val)) : SourceLigationGenerated n T w := by
  obtain ⟨hp0, hpn, kp, hp⟩ := hp
  obtain ⟨hs0, hsn, ks, hs⟩ := hs
  have hi : 0 < i.val ∧ i.val < w.length := Finset.mem_Ioo.mp i.property
  let r := ligationCutReaction n w hn i
  have hl : reactionLeft r ∈ revClosureAt (binaryPolymerCRS n 2) T (max kp ks) := by
    rw [ligationCutReaction_left n w hn i hp0 hpn]
    exact revClosureAt_mono_time _ _ (Nat.le_max_left _ _) hp
  have hh : reactionRight r ∈ revClosureAt (binaryPolymerCRS n 2) T (max kp ks) := by
    rw [ligationCutReaction_right n w hn i hs0 hsn]
    exact revClosureAt_mono_time _ _ (Nat.le_max_right _ _) hs
  have he : RevEnabledLhs (binaryPolymerCRS n 2)
      (revClosureAt (binaryPolymerCRS n 2) T (max kp ks)) r := by
    simpa [RevEnabledLhs, binaryPolymerCRS, Finset.insert_subset_iff] using And.intro hl hh
  have h0 : 1 ≤ w.length := by omega
  refine ⟨h0, hn, max kp ks+1, ?_⟩
  rw [← ligationCutReaction_product n w hn i h0]
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨r, hr, Finset.mem_union_left _ ?_⟩
  rw [if_pos he]
  exact Finset.mem_singleton_self _

/-- Every true raw bit used by the schedule is an available source channel. -/
def SourceLigationRawSupported (n : Nat) (T : Finset (Reaction n)) :
    (words : List LigationWord) → LigationRawConfiguration words → Prop
  | [], _ => True
  | w :: rest, cfg =>
      (∀ i : ligationCuts w, cfg.1 i = true →
        ∃ hn : w.length ≤ n, ligationCutReaction n w hn i ∈ T) ∧
      SourceLigationRawSupported n T rest cfg.2

/-- Raw success transfers to actual reversible closure, without promoting
the supplied nucleus to additional physical food. -/
theorem ligationRawKnown_source_generated (n : Nat) (T : Finset (Reaction n))
    (words : List LigationWord) (cfg : LigationRawConfiguration words)
    (known : Finset LigationWord) (hsupp : SourceLigationRawSupported n T words cfg)
    (hknown : ∀ u ∈ known, SourceLigationGenerated n T u) :
    ∀ u ∈ ligationRawKnown words cfg known, SourceLigationGenerated n T u := by
  classical
  induction words generalizing known with
  | nil => exact hknown
  | cons w rest ih =>
    change (∀ i : ligationCuts w, cfg.1 i = true →
      ∃ hn : w.length ≤ n, ligationCutReaction n w hn i ∈ T) ∧
      SourceLigationRawSupported n T rest cfg.2 at hsupp
    dsimp only [ligationRawKnown]
    apply ih cfg.2 _ hsupp.2
    by_cases hf : fullLigationRowFails known w cfg.1
    · simpa only [if_pos hf] using hknown
    · rw [if_neg hf]
      have hhit := hf
      simp only [fullLigationRowFails] at hhit
      push Not at hhit
      obtain ⟨i, hi, hb⟩ := hhit
      have htrue : cfg.1 i = true := Bool.eq_true_of_not_eq_false hb
      obtain ⟨hn, hr⟩ := hsupp.1 i htrue
      have ha := (Finset.mem_filter.mp hi).2
      have hp := (Finset.mem_filter.mp ha).2.1
      have hs := (Finset.mem_filter.mp ha).2.2
      have hw := sourceLigationGenerated_of_cut n T w hn i hr (hknown _ hp) (hknown _ hs)
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hw
      · exact hknown u hu

end
end PowerLawSmallRAF

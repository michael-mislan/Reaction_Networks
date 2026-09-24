import proofs.PowerLawSmallRAF.BoundedRawLigationWitness
import proofs.PowerLawSmallRAF.SourceNucleusSelection

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
noncomputable section

/-- A generated fixed seed replaces all marking requirements below its
cutoff. No freshness or independence from the seed event is assumed. -/
theorem source_seeded_one_cut_nucleus_generated (n m L : Nat) (hLn : L ≤ n)
    (T : Finset (Reaction n))
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m → SourceLigationGenerated n T w)
    (hcut : ∀ (w : LigationWord), m < w.length → ∀ hL : w.length ≤ L,
      ∃ i : ligationCuts w, ligationCutReaction n w (hL.trans hLn) i ∈ T) :
    ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n T w := by
  intro w
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h k ih =>
    intro h0 hL
    have h0w : 1 ≤ w.length := by omega
    have hLw : w.length ≤ L := by omega
    by_cases hm : w.length ≤ m
    · exact hseed w h0w hm
    · obtain ⟨i,hi⟩ := hcut w (by omega) hLw
      have hic := Finset.mem_Ioo.mp i.property
      apply sourceLigationGenerated_of_cut n T w (hLw.trans hLn) i hi
      · have hlen : (w.take i.val).length = i.val := List.length_take_of_le (by omega)
        apply ih i.val (by omega) (w.take i.val) hlen <;> omega
      · have hlen : (w.drop i.val).length = w.length-i.val := List.length_drop
        apply ih (w.length-i.val) (by omega) (w.drop i.val) hlen <;> omega

/-- Select real additional catalyst owners only above the fixed seed. The
base support and its owners must be retained separately in RAF assembly. -/
theorem source_seeded_nucleus_bounded_selection {Owner : Type*} [DecidableEq Owner]
    (n m L : Nat) (hLn : L ≤ n) (B : Finset (Reaction n))
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m → SourceLigationGenerated n B w)
    (A : Owner → Finset (Reaction n)) (W : Finset LigationWord)
    (hW : ∀ w, w ∈ W ↔ m < w.length ∧ w.length ≤ L)
    (hmark : ∀ w ∈ W, ∃ (hn : w.length ≤ n) (i : ligationCuts w)
      (x : Owner), ligationCutReaction n w hn i ∈ A x) :
    ∃ (S : Finset (Reaction n)) (C : Finset Owner),
      S.card ≤ W.card ∧ C.card ≤ W.card ∧ (B ∪ S).card ≤ B.card+W.card ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n (B ∪ S) w) := by
  classical
  have hex (v : W) : ∃ z : Reaction n × Owner,
      z.1 ∈ A z.2 ∧ ∃ (hn : v.val.length ≤ n) (i : ligationCuts v.val),
        z.1 = ligationCutReaction n v.val hn i := by
    obtain ⟨hn,i,x,hx⟩ := hmark v.val v.property
    exact ⟨⟨ligationCutReaction n v.val hn i,x⟩,hx,hn,i,rfl⟩
  let choice : W → Reaction n × Owner := fun v => Classical.choose (hex v)
  have hchoice (v : W) : (choice v).1 ∈ A (choice v).2 ∧
      ∃ (hn : v.val.length ≤ n) (i : ligationCuts v.val),
        (choice v).1 = ligationCutReaction n v.val hn i := Classical.choose_spec (hex v)
  let S := Finset.univ.image (fun v : W => (choice v).1)
  let C := Finset.univ.image (fun v : W => (choice v).2)
  have hS : S.card ≤ W.card := Finset.card_image_le.trans (by simp)
  refine ⟨S,C,hS,Finset.card_image_le.trans (by simp),
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left hS _),?_,?_,?_⟩
  · intro r hr
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hr
    exact ⟨(choice v).2,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,(hchoice v).1⟩
  · intro x hx
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(choice v).1,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,(hchoice v).1⟩
  · apply source_seeded_one_cut_nucleus_generated n m L hLn (B ∪ S)
    · intro w h0 hm
      exact sourceLigationGenerated_mono n B (B ∪ S) Finset.subset_union_left w (hseed w h0 hm)
    · intro w hm hL
      let v : W := ⟨w,(hW w).mpr ⟨hm,hL⟩⟩
      obtain ⟨hn,i,hi⟩ := (hchoice v).2
      refine ⟨i,Finset.mem_union_right _ ?_⟩
      have hh : (choice v).1 ∈ S := Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
      simpa only [hi] using hh

end
end PowerLawSmallRAF

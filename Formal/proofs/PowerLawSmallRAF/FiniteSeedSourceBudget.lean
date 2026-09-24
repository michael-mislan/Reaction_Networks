import proofs.PowerLawSmallRAF.FiniteSeedSourceTransport
import proofs.PowerLawSmallRAF.BernoulliUnionLaw

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section

def sourceLiftSeedReaction (N n : Nat) (hNn : N ≤ n) (r : Reaction N) : Reaction n :=
  ⟨⟨r.1.val,r.1.isLt.trans_le hNn⟩,r.2⟩

/-- Retaining a fixed finite witness cap costs at most that cap's literal
reaction catalogue, independently of the ambient source horizon. -/
theorem sourceSeedRestriction_card_le (n N : Nat) (hNn : N ≤ n)
    (H : Finset (Reaction n)) :
    (sourceSeedRestriction n N H).card ≤ Fintype.card (Reaction N) := by
  classical
  have hs : sourceSeedRestriction n N H ⊆ Finset.univ.image (sourceLiftSeedReaction N n hNn) := by
    intro r hr
    have hcap := (Finset.mem_filter.mp hr).2
    have hk : r.1.val < N := by
      change r.1.val+1 ≤ N at hcap
      omega
    let s : Reaction N := ⟨⟨r.1.val,hk⟩,r.2⟩
    refine Finset.mem_image.mpr ⟨s,Finset.mem_univ _,?_⟩
    rcases r with ⟨⟨k,hk⟩,p⟩
    rfl
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

/-- The transported fixed seed has a bounded base and real low-field
catalyst owners. Their later generation remains an explicit RAF obligation. -/
theorem source_finite_seed_owner_selection {Owner : Type*} [Fintype Owner] [DecidableEq Owner]
    (n N m : Nat) (hNn : N ≤ n) (A : Owner → Finset (Reaction n))
    (hseed : ∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m →
      FiniteReversibleGenerated N 2 (sourceSeedField n (bernoulliRowsUnion A)) w) :
    ∃ (B : Finset (Reaction n)) (C : Finset Owner),
      B ⊆ bernoulliRowsUnion A ∧ B.card ≤ Fintype.card (Reaction N) ∧
      C.card ≤ Fintype.card (Reaction N) ∧
      (∀ r ∈ B, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ B, r ∈ A x) ∧
      (∀ w : LigationWord, 1 ≤ w.length → w.length ≤ m → SourceLigationGenerated n B w) := by
  classical
  let B := sourceSeedRestriction n N (bernoulliRowsUnion A)
  have hB : B ⊆ bernoulliRowsUnion A := Finset.filter_subset _ _
  have hex (r : B) : ∃ x : Owner, r.val ∈ A x := by
    obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp (hB r.property)
    exact ⟨x,hx⟩
  let owner : B → Owner := fun r => Classical.choose (hex r)
  have howner (r : B) : r.val ∈ A (owner r) := Classical.choose_spec (hex r)
  let C := Finset.univ.image owner
  have hcard := sourceSeedRestriction_card_le n N hNn (bernoulliRowsUnion A)
  have hC : C.card ≤ B.card := Finset.card_image_le.trans (by simp)
  refine ⟨B,C,hB,hcard,hC.trans hcard,?_,?_,?_⟩
  · intro r hr
    let v : B := ⟨r,hr⟩
    exact ⟨owner v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,howner v⟩
  · intro x hx
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨r.val,r.property,howner r⟩
  · intro w h0 hm
    exact source_finite_seed_transport n N hNn _ w (hseed w h0 hm)

end
end PowerLawSmallRAF

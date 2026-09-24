import proofs.PowerLawSmallRAF.SourceLowNucleusRetainedLaw
import proofs.PowerLawSmallRAF.TargetUnionConditions

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A total selector depending only on the degree vector and retained low
rows. Empty on failure, it never inspects the high field. -/
def sourceLowNucleusSelection (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) :
    Finset (Reaction n) × Finset (SourceLowOwnerGroup n d) :=
  if h : L ≤ n ∧ SourceNucleusMarked n L (bernoulliRowsUnion A) then
    let hex := sourceLowRowsNucleus_selection n L h.1 d A h.2
    ⟨Classical.choose hex,Classical.choose (Classical.choose_spec hex)⟩
  else ⟨∅,∅⟩

theorem sourceLowNucleusSelection_spec (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) (hLn : L ≤ n)
    (hmark : SourceNucleusMarked n L (bernoulliRowsUnion A)) :
    let S := (sourceLowNucleusSelection n L d A).1
    let C := (sourceLowNucleusSelection n L d A).2
    S.card ≤ 2^(L+1) ∧ C.card ≤ 2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) := by
  simp only [sourceLowNucleusSelection,dif_pos (And.intro hLn hmark)]
  exact Classical.choose_spec (Classical.choose_spec
    (sourceLowRowsNucleus_selection n L hLn d A hmark))

theorem sourceLowNucleusSelection_budgets (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) :
    (sourceLowNucleusSelection n L d A).1.card ≤ 2^(L+1) ∧
      (sourceLowNucleusSelection n L d A).2.card ≤ 2^(L+1) := by
  by_cases h : L ≤ n ∧ SourceNucleusMarked n L (bernoulliRowsUnion A)
  · have hs := sourceLowNucleusSelection_spec n L d A h.1 h.2
    exact ⟨hs.1,hs.2.1⟩
  · simp [sourceLowNucleusSelection,h]

def sourceLowNucleusOwnerWords (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) : Finset LigationWord :=
  (sourceLowNucleusSelection n L d A).2.image (fun x => sourceOwnerWord x.val)

theorem sourceLowNucleusOwnerWords_card_le (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) :
    (sourceLowNucleusOwnerWords n L d A).card ≤ 2^(L+1) :=
  Finset.card_image_le.trans (sourceLowNucleusSelection_budgets n L d A).2

theorem sourceLowNucleusOwnerWords_length_le (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) :
    ∀ w ∈ sourceLowNucleusOwnerWords n L d A, w.length ≤ n := by
  intro w hw
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hw
  rw [sourceOwnerWord_length]
  have hx := x.val.1.isLt
  unfold molLength
  omega

theorem sourceLowNucleusOwnerWords_has_mark (n L : Nat) (d : SourceDegreeConfig n)
    (A : SourceLowOwnerGroup n d → Finset (Reaction n)) :
    ∀ w ∈ sourceLowNucleusOwnerWords n L d A, ∃ x : SourceLowOwnerGroup n d,
      sourceOwnerWord x.val = w ∧ (A x).Nonempty := by
  intro w hw
  by_cases h : L ≤ n ∧ SourceNucleusMarked n L (bernoulliRowsUnion A)
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨r,_,hr⟩ := (sourceLowNucleusSelection_spec n L d A h.1 h.2).2.2.2.1 x hx
    exact ⟨x,rfl,r,hr⟩
  · simp [sourceLowNucleusOwnerWords,sourceLowNucleusSelection,h] at hw

theorem sourceLowRows_actualNucleus_eventually_lower :
    ∀ᶠ n in atTop, sourceNucleusProbabilityFloor/2 ≤
      sourceLowRowsNucleusMass n (targetNucleusLength n) := by
  apply sourceLowRowsNucleusMass_eventually_lower
  filter_upwards [targetUnion_eventual_conditions] with n hn
  exact hn.2.2.2.1.trans (Nat.div_le_self _ _)

end
end PowerLawSmallRAF

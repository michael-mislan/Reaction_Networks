import proofs.PowerLawSmallRAF.SourceLowNucleusAverage

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def sourceLowRowsNucleusMass (n L : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : SourceLowOwnerGroup n d → Finset (Reaction n),
      bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
        (if SourceNucleusMarked n L (bernoulliRowsUnion A) then 1 else 0)

theorem sourceLowRowsNucleusMass_eq (n L : Nat) :
    sourceLowRowsNucleusMass n L = sourceLowNucleusMass n L := by
  unfold sourceLowRowsNucleusMass sourceLowNucleusMass
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact bernoulliRows_union_expectation
    (fun x : SourceLowOwnerGroup n d => sourceBandBernoulliParameter n d x.val)
    (fun H => if SourceNucleusMarked n L H then 1 else 0)

theorem sourceLowRowsNucleusMass_eventually_lower (L : Nat → Nat)
    (hL : ∀ᶠ n in atTop, L n ≤ n) :
    ∀ᶠ n in atTop, sourceNucleusProbabilityFloor/2 ≤ sourceLowRowsNucleusMass n (L n) := by
  simp_rw [sourceLowRowsNucleusMass_eq]
  exact sourceLowNucleusMass_eventually_lower L hL

/-- On the nucleus event the chosen support uses actual retained low-owner
rows. No extra food or catalytic ownership is invented. -/
theorem sourceLowRowsNucleus_selection (n L : Nat) (hLn : L ≤ n)
    (d : SourceDegreeConfig n) (A : SourceLowOwnerGroup n d → Finset (Reaction n))
    (hmark : SourceNucleusMarked n L (bernoulliRowsUnion A)) :
    ∃ (S : Finset (Reaction n)) (C : Finset (SourceLowOwnerGroup n d)),
      S.card ≤ 2^(L+1) ∧ C.card ≤ 2^(L+1) ∧
      (∀ r ∈ S, ∃ x ∈ C, r ∈ A x) ∧
      (∀ x ∈ C, ∃ r ∈ S, r ∈ A x) ∧
      (∀ w, 1 ≤ w.length → w.length ≤ L → SourceLigationGenerated n S w) := by
  apply source_nucleus_selection_power_budget n L hLn A
  intro w hw
  obtain ⟨hn,i,hi⟩ := hmark w hw
  obtain ⟨x,_,hx⟩ := Finset.mem_biUnion.mp hi
  exact ⟨hn,i,x,hx⟩

end
end PowerLawSmallRAF

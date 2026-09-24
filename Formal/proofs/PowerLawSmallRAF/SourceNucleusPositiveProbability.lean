import proofs.PowerLawSmallRAF.SourceNucleusMarkLaw
import proofs.PowerLawSmallRAF.NucleusFailureSum

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def SourceNucleusMarked (n L : Nat) (H : Finset (Reaction n)) : Prop :=
  ∀ w ∈ sourceNonfoodNucleusWords L, ∃ (hn : w.length ≤ n) (i : ligationCuts w),
    ligationCutReaction n w hn i ∈ H

def sourceNucleusMarkMass (p : ℝ) (n L : Nat) : ℝ :=
  ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
    (if SourceNucleusMarked n L H then 1 else 0)

theorem sourceNucleusMarkMass_eq_product (p : ℝ) (n L : Nat) (hLn : L ≤ n) :
    sourceNucleusMarkMass p n L =
      ∏ w ∈ sourceNonfoodNucleusWords L, (1-(1-p)^(w.length-1)) := by
  let words := (sourceNonfoodNucleusWords L).toList
  have hb : ∀ w ∈ words, w.length ≤ n := by
    intro w hw
    exact ((mem_sourceNonfoodNucleusWords L w).mp (Finset.mem_toList.mp hw)).2.trans hLn
  have he (H : Finset (Reaction n)) :
      (∀ w (hw : w ∈ words), ∃ i : ligationCuts w,
        ligationCutReaction n w (hb w hw) i ∈ H) ↔ SourceNucleusMarked n L H := by
    constructor
    · intro hh w hw
      exact ⟨hb w (Finset.mem_toList.mpr hw),hh w (Finset.mem_toList.mpr hw)⟩
    · intro hh w hw
      obtain ⟨hn,i,hi⟩ := hh w (Finset.mem_toList.mp hw)
      exact ⟨i,hi⟩
  have hh := source_nucleus_mark_probability p n words hb (Finset.nodup_toList _)
  simp_rw [he] at hh
  simpa only [sourceNucleusMarkMass,words,Finset.prod_map_toList] using hh

/-- Uniform in the nucleus size, for the actual iid source-channel field. -/
theorem sourceNucleusMarkMass_positive_lower (p : ℝ) (hp : 1/2 < p) (hp1 : p ≤ 1)
    (n L : Nat) (hLn : L ≤ n) :
    0 < Real.exp (-4/(2*p-1)) ∧
      Real.exp (-4/(2*p-1)) ≤ sourceNucleusMarkMass p n L := by
  have h := nucleus_finite_product_positive (1-p) (by linarith) (by linarith) L
  rw [sourceNucleusMarkMass_eq_product p n L hLn]
  have he : 1-2*(1-p) = 2*p-1 := by ring
  simpa only [he] using h

theorem sourceNucleusMarkMass_uniform_lower (q p : ℝ) (hq : 1/2 < q)
    (hqp : q ≤ p) (hp1 : p ≤ 1) (n L : Nat) (hLn : L ≤ n) :
    0 < Real.exp (-4/(2*q-1)) ∧
      Real.exp (-4/(2*q-1)) ≤ sourceNucleusMarkMass p n L := by
  refine ⟨Real.exp_pos _,?_⟩
  apply le_trans _ (sourceNucleusMarkMass_positive_lower p (hq.trans_le hqp) hp1 n L hLn).2
  apply Real.exp_le_exp.mpr
  have hh : 4/(2*p-1) ≤ 4/(2*q-1) :=
    div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  simpa only [neg_div] using neg_le_neg hh

end
end PowerLawSmallRAF

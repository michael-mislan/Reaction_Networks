import proofs.PowerLawSmallRAF.FixedSeedGeometricTail
import proofs.PowerLawSmallRAF.SourceNucleusMarkLaw

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem list_mark_failure_le_sum (xs : List ℝ)
    (hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    0 ≤ (xs.map (fun x => 1-x)).prod ∧ (xs.map (fun x => 1-x)).prod ≤ 1 ∧
      1-(xs.map (fun x => 1-x)).prod ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    refine ⟨mul_nonneg (by linarith) ht.1,?_,?_⟩
    · nlinarith only [ht.2.1,mul_nonneg hh.1 ht.1]
    · nlinarith only [ht.2.2,mul_nonneg hh.1 (sub_nonneg.mpr ht.2.1)]

def SourceAboveSeedMarked (n m L : Nat) (H : Finset (Reaction n)) : Prop :=
  ∀ w ∈ sourceAboveSeedWords m L, ∃ (hn : w.length ≤ n) (i : ligationCuts w),
    ligationCutReaction n w hn i ∈ H

def sourceAboveSeedMarkMass (p : ℝ) (n m L : Nat) : ℝ :=
  ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
    (if SourceAboveSeedMarked n m L H then 1 else 0)

def sourceAboveSeedFailureMass (p : ℝ) (n m L : Nat) : ℝ :=
  ∑ H : Finset (Reaction n), if ¬ SourceAboveSeedMarked n m L H then bernoulliSubsetRowWeight p H else 0

theorem sourceAboveSeedMarkMass_eq_product (p : ℝ) (n m L : Nat) (hLn : L ≤ n) :
    sourceAboveSeedMarkMass p n m L = ∏ w ∈ sourceAboveSeedWords m L, (1-(1-p)^(w.length-1)) := by
  let words := (sourceAboveSeedWords m L).toList
  have hb : ∀ w ∈ words, w.length ≤ n := by
    intro w hw
    exact ((mem_sourceAboveSeedWords m L w).mp (Finset.mem_toList.mp hw)).2.trans hLn
  have he (H : Finset (Reaction n)) :
      (∀ w (hw : w ∈ words), ∃ i : ligationCuts w,
        ligationCutReaction n w (hb w hw) i ∈ H) ↔ SourceAboveSeedMarked n m L H := by
    constructor
    · intro hh w hw
      exact ⟨hb w (Finset.mem_toList.mpr hw),hh w (Finset.mem_toList.mpr hw)⟩
    · intro hh w hw
      obtain ⟨hn,i,hi⟩ := hh w (Finset.mem_toList.mp hw)
      exact ⟨i,hi⟩
  have hh := source_nucleus_mark_probability p n words hb (Finset.nodup_toList _)
  simp_rw [he] at hh
  simpa only [sourceAboveSeedMarkMass,words,Finset.prod_map_toList] using hh

theorem sourceAboveSeedFailureMass_eq (p : ℝ) (n m L : Nat) :
    sourceAboveSeedFailureMass p n m L = 1-sourceAboveSeedMarkMass p n m L := by
  calc
    _ = ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight p H *
        (1-(if SourceAboveSeedMarked n m L H then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro H _
      by_cases hh : SourceAboveSeedMarked n m L H <;> simp [hh]
    _ = _ := by
      simp_rw [mul_sub,mul_one]
      rw [Finset.sum_sub_distrib,sum_bernoulliSubsetRowWeight]
      rfl

/-- Uniform in the growing cutoff L, with an error tending to zero as the
fixed seed cutoff m increases. It is an unconditional marked-field bound. -/
theorem sourceAboveSeedFailureMass_bound (p : ℝ) (hp : 1/2 < p) (hp1 : p ≤ 1)
    (n m L : Nat) (hLn : L ≤ n) :
    sourceAboveSeedFailureMass p n m L ≤ 2*(2*(1-p))^m/(1-2*(1-p)) := by
  rw [sourceAboveSeedFailureMass_eq,sourceAboveSeedMarkMass_eq_product p n m L hLn]
  let xs := (sourceAboveSeedWords m L).toList.map (fun w => (1-p)^(w.length-1))
  have hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨pow_nonneg (by linarith) _,pow_le_one₀ (by linarith) (by linarith)⟩
  have hh := (list_mark_failure_le_sum xs hx).2.2
  have hprod : (xs.map (fun x => 1-x)).prod =
      ∏ w ∈ sourceAboveSeedWords m L, (1-(1-p)^(w.length-1)) := by
    simp only [xs,List.map_map,Function.comp_def,Finset.prod_map_toList]
  rw [hprod] at hh
  apply hh.trans
  simpa only [xs,Finset.sum_map_toList] using
    sourceAboveSeedWords_failure_sum_le (1-p) (by linarith) (by linarith) m L

end
end PowerLawSmallRAF

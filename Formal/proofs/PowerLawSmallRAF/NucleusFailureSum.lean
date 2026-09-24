import proofs.PowerLawSmallRAF.SourceNucleusWords
import proofs.PowerLawSmallRAF.NucleusProductLower

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete
open scoped BigOperators
noncomputable section

theorem nucleus_weighted_geom_identity (r : ℝ) (L : Nat) :
    (∑ k : Fin L, (2 : ℝ)^(k.val+1)*r^k.val)*(1-2*r) = 2*(1-(2*r)^L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [add_mul,ih,pow_succ,mul_pow,pow_succ]
    ring

theorem nucleus_molecule_failure_sum_le (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2)
    (L : Nat) : (∑ x : Molecule L, r^x.1.val) ≤ 2/(1-2*r) := by
  have hp : 0 < 1-2*r := by linarith
  have hid := nucleus_weighted_geom_identity r L
  have hs : (∑ x : Molecule L, r^x.1.val) =
      ∑ k : Fin L, (2 : ℝ)^(k.val+1)*r^k.val := by
    rw [Fintype.sum_sigma]
    simp [Word]
  rw [hs]
  apply (le_div_iff₀ hp).mpr
  rw [hid]
  have hpow : 0 ≤ (2*r)^L := pow_nonneg (by positivity) _
  linarith

/-- A deliberately loose uniform bound: summing also over food words makes
the geometric estimate simpler without sacrificing a positive constant. -/
theorem nucleus_failure_sum_le (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2) (L : Nat) :
    (∑ w ∈ sourceNonfoodNucleusWords L, r^(w.length-1)) ≤ 2/(1-2*r) := by
  classical
  unfold sourceNonfoodNucleusWords
  calc
    _ ≤ ∑ w ∈ Finset.univ.image (@sourceOwnerWord L), r^(w.length-1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun w _ _ => pow_nonneg hr _)
    _ = ∑ x : Molecule L, r^x.1.val := by
      rw [Finset.sum_image (fun x _ y _ h => sourceOwnerWord_injective h)]
      apply Finset.sum_congr rfl
      intro x _
      rw [sourceOwnerWord_length]
      simp [molLength]
    _ ≤ _ := nucleus_molecule_failure_sum_le r hr hr2 L

theorem nucleus_finite_product_positive (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2) (L : Nat) :
    0 < Real.exp (-4/(1-2*r)) ∧
      Real.exp (-4/(1-2*r)) ≤
        ∏ w ∈ sourceNonfoodNucleusWords L, (1-r^(w.length-1)) := by
  classical
  let xs := (sourceNonfoodNucleusWords L).toList.map (fun w => r^(w.length-1))
  have hx : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1/2 := by
    intro x hx
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hx
    have hlen := (mem_sourceNonfoodNucleusWords L w).mp (Finset.mem_toList.mp hw)
    refine ⟨pow_nonneg hr _,?_⟩
    have hle : r^(w.length-1) ≤ r^1 :=
      pow_le_pow_of_le_one hr (by linarith) (by omega)
    rw [pow_one] at hle
    exact hle.trans hr2.le
  have hs : xs.sum ≤ 2/(1-2*r) := by
    simpa only [xs,Finset.sum_map_toList] using nucleus_failure_sum_le r hr hr2 L
  have h := nucleus_product_uniform_lower xs (2/(1-2*r)) hx hs
  have he : -2*(2/(1-2*r)) = -4/(1-2*r) := by ring
  simpa only [he,xs,List.map_map,Function.comp_def,Finset.prod_map_toList] using h

end
end PowerLawSmallRAF

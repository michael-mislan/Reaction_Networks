import proofs.StoredRedCells.S7Bridge
import Mathlib.Algebra.BigOperators.Fin

/-! Connect checked sparse data blocks to a finite reaction family.
This uniform adapter does not assert that a particular data file is complete. -/
namespace StoredRedCells.S7Certificate
noncomputable section
open Finset

def columnAt (chunks : List (List Column)) (j : Fin chunks.flatten.length) : Column :=
  chunks.flatten.get j

theorem sum_cost_chunks (chunks : List (List Column)) :
    (∑ j : Fin chunks.flatten.length, cost (columnAt chunks j)) =
      (chunks.map (fun rs => (rs.map cost).sum)).sum := by
  unfold columnAt
  rw [← List.sum_ofFn]
  change (List.ofFn (cost ∘ chunks.flatten.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  simp [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]

theorem column_indices (chunks : List (List Column))
    (hidx : chunks.all (fun rs => rs.all (fun r =>
      r.terms.all (fun p => decide (p.1 < 10411)))) = true) :
    ∀ j, ∀ p ∈ (columnAt chunks j).terms, p.1 < 10411 := by
  have h : ∀ rs ∈ chunks, ∀ r ∈ rs, ∀ p ∈ r.terms, p.1 < 10411 := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hidx
  intro j p hp
  have hm : columnAt chunks j ∈ chunks.flatten := List.get_mem _ _
  obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp hm
  exact h rs hrs _ hr p hp

theorem column_supplies (chunks : List (List Column))
    (hs : chunks.all (fun rs => rs.all (fun r => decide (0 ≤ r.supply))) = true) :
    ∀ j, (0 : ℝ) ≤ (columnAt chunks j).supply := by
  have h : ∀ rs ∈ chunks, ∀ r ∈ rs, (0 : ℤ) ≤ r.supply := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hs
  intro j
  have hm : columnAt chunks j ∈ chunks.flatten := List.get_mem _ _
  obtain ⟨rs, hrs, hr⟩ := List.mem_flatten.mp hm
  exact_mod_cast h rs hrs _ hr

theorem inventory_from_chunks (chunks : List (List Column))
    (xi : Fin chunks.flatten.length → ℝ) (x0 ell : Fin 10411 → ℝ)
    (T W S B K : ℝ) (hW : 0 < W) (hS : 0 < S) (hB : 0 < B)
    (hidx : chunks.all (fun rs => rs.all (fun r =>
      r.terms.all (fun p => decide (p.1 < 10411)))) = true)
    (hs : chunks.all (fun rs => rs.all (fun r => decide (0 ≤ r.supply))) = true)
    (hcost : (((chunks.map (fun rs => (rs.map cost).sum)).sum : ℤ) : ℝ) /
      (W*S*B) ≤ K)
    (hT : 0 ≤ T)
    (hfloor : ∀ i, (chemicalWeight i.val : ℝ) ≠ 0 →
      ell i ≤ x0 i + ∑ j, (matrixEntry (columnAt chunks j) i / S) * xi j)
    (haux : ∀ i, (auxiliaryWeight i.val : ℝ) ≠ 0 →
      ∑ j, (matrixEntry (columnAt chunks j) i / S) * xi j = 0)
    (hL : ∀ j, ((columnAt chunks j).lower : ℝ) / B * T ≤ xi j)
    (hU : ∀ j, xi j ≤ ((columnAt chunks j).upper : ℝ) / B * T) :
    (∑ j, (((columnAt chunks j).objective : ℝ) / (W*S)) * xi j) ≤
      (∑ i, ((chemicalWeight i.val : ℝ) / W) * (x0 i - ell i)) +
      K*T +
      (∑ j, (((columnAt chunks j).supply : ℝ) / (W*S)) * max (-xi j) 0) := by
  have hc : (∑ j, (cost (columnAt chunks j) : ℝ)) =
      (((chunks.map (fun rs => (rs.map cost).sum)).sum : ℤ) : ℝ) := by
    exact_mod_cast sum_cost_chunks chunks
  have h := inventory_physical (columnAt chunks) xi x0 ell T W S B
    hW hS hB (column_indices chunks hidx) hT (column_supplies chunks hs)
    hfloor haux hL hU
  rw [hc] at h
  have hk := mul_le_mul_of_nonneg_right hcost hT
  linarith only [h, hk]

end
end StoredRedCells.S7Certificate

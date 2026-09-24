import proofs.InheritedCellAssay.ObservationBridge
import proofs.InheritedCellAssay.FounderMoments
import proofs.InheritedCellAssay.JointKernel

namespace InheritedCellAssay
open scoped BigOperators

theorem sister_mean_response (F k : ℕ) (hk : k ≤ F) :
    sourceExpectation k (fun s => (((sisterEndpoint F k s).filter id).length : ℚ)) =
      8*F := by
  calc
    _ = sourceExpectation k (fun s => 16*(s.card : ℚ)+8*(F-k : ℕ)) := by
      congr 1
      funext s
      rw [sister_endpoint_response]
      push_cast
      ring
    _ = 16*((k : ℚ)/2)+8*(F-k : ℕ) := source_affine k _ _
    _ = 8*F := by rw [Nat.cast_sub hk]; ring

theorem sister_mean_count (F k : ℕ) (hk : k ≤ F) :
    sourceExpectation k (fun s => ((sisterEndpoint F k s).length : ℚ)) = 9*F := by
  calc
    _ = sourceExpectation k (fun s => 14*(s.card : ℚ)+(9*F-7*k)) := by
      congr 1
      funext s
      have hc : s.card ≤ k := by simpa using Finset.card_le_univ s
      rw [sister_endpoint_count]
      push_cast
      rw [Nat.cast_sub hk, Nat.cast_sub hc]
      ring
    _ = 14*((k : ℚ)/2)+(9*F-7*k) := source_affine k _ _
    _ = 9*F := by ring

noncomputable def populationTarget (w : Fin 31 → ℚ) : ℚ :=
  (∑ k, w k * sourceExpectation k (fun s =>
    (((sisterEndpoint 30 k s).filter id).length : ℚ))) /
  (∑ k, w k * sourceExpectation k (fun s => ((sisterEndpoint 30 k s).length : ℚ)))

theorem population_target_eq (w : Fin 31 → ℚ) (hn : ∑ k, w k = 1) :
    populationTarget w = 8/9 := by
  unfold populationTarget
  have hr (k : Fin 31) := sister_mean_response 30 k (by omega)
  have hc (k : Fin 31) := sister_mean_count 30 k (by omega)
  simp_rw [hr, hc]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hn]
  norm_num

theorem sister_endpoint_nonempty (k : Fin 31) (s : Finset (Fin k.val)) :
    0 < (sisterEndpoint 30 k s).length := by
  rw [sister_endpoint_count]
  have hc : s.card ≤ k.val := by simpa using Finset.card_le_univ s
  have hk := k.isLt
  omega

/-- The finite-assay theorem: a complete mixture of actual paired offspring
sources, its derived descendant-weighted target, its uniform accuracy guarantee,
and absence of a zero-denominator event. All weights may be unknown. -/
theorem main_resolution (w : Fin 31 → ℚ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) :
    populationTarget w = 8/9 ∧
    actualMixtureRisk w ≤ 2061197/67108864 ∧
    actualMixtureRisk w < 1/20 ∧
    (∀ k : Fin 31, ∀ s : Finset (Fin k.val), 0 < (sisterEndpoint 30 k s).length) := by
  exact ⟨population_target_eq w hn, (robust_resolution w hw hn).1,
    (robust_resolution w hw hn).2, sister_endpoint_nonempty⟩

end InheritedCellAssay

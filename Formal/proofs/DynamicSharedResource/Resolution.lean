import proofs.DynamicSharedResource.PhysicalService
import proofs.DynamicSharedResource.Regularity

namespace DynamicSharedResource.Certificate
noncomputable section
open Set Metric
open scoped BigOperators

theorem modal_smooth : ContDiffOn ℝ 1 modalField (closedBall 0 1) := by
  intro a ha
  have hab : InCube 1 a := (cube_iff_norm 1 (by norm_num) a).mpr
    (by simpa only [mem_closedBall,dist_zero_right] using ha)
  have hz : 873/10-reconstruct a 0 ≠ 0 := by
    have h := displaced_denominator 1 le_rfl a hab
    change 873/10-(center 0+basis.mulVec a 0) ≠ 0
    linarith
  have hrec : ContDiffAt ℝ 1 reconstruct a := (affine_contDiff center basis).contDiffAt
  have hn := (nominal_contDiffAt (reconstruct a) hz).comp a hrec
  have hlin : ContDiff ℝ 1 (fun u : State => inverse.mulVec u) := by
    simpa only [zero_add] using affine_contDiff (0:State) inverse
  exact (hlin.contDiffAt.comp a hn).contDiffWithinAt

theorem source_solution_exists (u₀ : State) (hu₀ : Prepared u₀) :
    ∃ u : ℝ → State, u 0=u₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t ∧ Physical (u t)) ∧
      ∀ t, 2000 ≤ t → InCube (1/2) (coordinates (u t)) ∧ 10 ≤ HG (u t) ∧ 4 ≤ HT (u t) := by
  obtain ⟨a,ha0,ha,hai⟩ := exists_captured_solution modalField modal_smooth
    nominal_face_decay (coordinates u₀) (prepared_in_outer u₀ hu₀)
  let u : ℝ → State := fun t => reconstruct (a t)
  have h0 : u 0=u₀ := by simp only [u,ha0,reconstruct_coordinates]
  refine ⟨u,h0,?_,?_⟩
  · intro t ht
    have h := mulVec_hasDerivAt basis a (modalField (a t)) t (ha t ht).1
    have he : basis.mulVec (modalField (a t))=nominal (u t) := by
      simp only [modalField,Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec,u]
    refine ⟨?_,outer_physical (a t) (ha t ht).2⟩
    rw [he] at h
    exact h.const_add center
  · intro t ht
    have hh := hai t ht
    exact ⟨by simpa only [u,coordinates_reconstruct] using hh,inner_service (a t) hh⟩

/-- The physical source and explicit preparation, not a hypothetical stable flow. -/
theorem nominal_recovery_and_service :
    Prepared preparation ∧ HT preparation < 4 ∧
    ∀ u₀ : State, Prepared u₀ →
      ∃ u : ℝ → State, u 0=u₀ ∧
        (∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t ∧ Physical (u t)) ∧
        ∀ t, 2000 ≤ t → InCube (1/2) (coordinates (u t)) ∧
          10 ≤ HG (u t) ∧ 4 ≤ HT (u t) :=
  ⟨preparation_mem,preparation_fails,source_solution_exists⟩

end
end DynamicSharedResource.Certificate

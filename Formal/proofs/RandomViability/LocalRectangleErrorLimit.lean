import proofs.RandomViability.LocalRectangleExcess
import proofs.PowerLawSmallRAF.SourceCriticalJointMiss

set_option Elab.async false
namespace RandomViability
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF
noncomputable section
set_option maxHeartbeats 70000

def localRectangleError (a : ℝ) (n Z M : ℕ) : ℝ :=
  (Z : ℝ)*((M : ℝ)/((sourceReactionCount n-M+1 : ℕ) : ℝ))^2*
    windowZipfSecondMoment a (sourceReactionCount n)+
  (Z : ℝ)^2*((M : ℝ)*windowZipfMean a (sourceReactionCount n)/
    ((sourceReactionCount n-M+1 : ℕ) : ℝ))^2

theorem local_rectangle_error_scaled_tendsto (Z M : ℕ) :
    Tendsto (fun n : ℕ => (sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n Z M)
      atTop (𝓝 0) := by
  by_cases hM : M = 0
  · subst M
    simp only [localRectangleError,Nat.cast_zero,zero_div,zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero]
    exact tendsto_const_nhds
  have hM0 : 0 < M := by omega
  have hE := sourceExactCriticalGatewayQuadraticError_scaled_tendsto_zero M hM0
  have hU := sourceExactCriticalGatewayUpper_scaled_tendsto M hM0
  have hXinv := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop).inv_tendsto_atTop
  have hu0 := hU.mul hXinv
  simp only [mul_zero] at hu0
  have hu : Tendsto (fun n : ℕ => (M : ℝ)*windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/
      ((sourceReactionCount n-M+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    apply hu0.congr'
    filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn
    have hX : (sourceMoleculeCount n : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hn)
    dsimp only [Pi.inv_apply,Function.comp_apply]
    field_simp
  have hh := (hE.const_mul (Z : ℝ)).add ((hU.mul hu).const_mul ((Z : ℝ)^2))
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall (fun n => by unfold localRectangleError; ring)

/-- Uniformity over bounded local cardinalities is finite symbolic summation,
not enumeration of source configurations or certificate replay. -/
theorem bounded_rectangle_error_scaled_tendsto (Zmax Mmax : ℕ) (Z M : ℕ → ℕ)
    (hZ : ∀ n,Z n ≤ Zmax) (hM : ∀ n,M n ≤ Mmax) :
    Tendsto (fun n : ℕ => (sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n (Z n) (M n))
      atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun n => ∑ z ∈ Finset.range (Zmax+1),∑ m ∈ Finset.range (Mmax+1),
    |(sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n z m|
  have hB : Tendsto B atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.range (Zmax+1)) (fun z _ =>
      tendsto_finsetSum (Finset.range (Mmax+1)) (fun m _ => (local_rectangle_error_scaled_tendsto z m).abs))
    simpa only [abs_zero,Finset.sum_const_zero] using hh
  have hb (n : ℕ) : |(sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n (Z n) (M n)| ≤ B n := by
    have hi := Finset.single_le_sum (fun m (_ : m ∈ Finset.range (Mmax+1)) =>
      abs_nonneg ((sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n (Z n) m))
      (Finset.mem_range.mpr (by have hh := hM n; omega : M n < Mmax+1))
    have ho := Finset.single_le_sum (fun z (_ : z ∈ Finset.range (Zmax+1)) =>
      Finset.sum_nonneg (fun m (_ : m ∈ Finset.range (Mmax+1)) =>
        abs_nonneg ((sourceMoleculeCount n : ℝ)*localRectangleError (2-2/(n : ℝ)) n z m)))
      (Finset.mem_range.mpr (by have hh := hZ n; omega : Z n < Zmax+1))
    exact hi.trans ho
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb n) hB

end
end RandomViability

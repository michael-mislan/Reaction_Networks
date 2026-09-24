import proofs.InheritedCellAssay.ScalarSourceCoverage
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace InheritedCellAssay.ScalarRateSource
open ScalarCount

theorem meanRatio_le_birth (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    meanRatio x ≤ 1+accumulatedBirth x := by
  have hder (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun s => 1+accumulatedBirth s-meanRatio s) (-death t*meanRatio t) t := by
    convert ((accumulatedBirth_derivative t).const_add 1).sub
      (meanRatio_derivative t ht.1) using 1
    ring
  have hc : ContinuousOn (fun s => 1+accumulatedBirth s-meanRatio s) (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.add accumulatedBirth_continuous).sub meanRatio_continuous |>.continuousOn
  have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1) hc
    (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => by
      have hd := (death_bounds t (interior_subset ht)).1
      have hmean := (meanRatio_bounds t (interior_subset ht)).1
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hmean)
  have h := hm hx (by norm_num) hx.2
  have h1 : 1+accumulatedBirth 1-meanRatio 1 = 0 := by
    norm_num [accumulatedBirth, meanRatio, den]
  change 1+accumulatedBirth 1-meanRatio 1 ≤ 1+accumulatedBirth x-meanRatio x at h
  rw [h1] at h
  linarith

theorem candidate_unit_bounds (x z : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ScalarBackward.candidate meanRatio accumulatedBirth z x ∈ Set.Icc (0 : ℝ) 1 := by
  have hm := (meanRatio_bounds x hx).1
  have ha := accumulatedBirth_nonneg x hx.2
  have hb := meanRatio_le_birth x hx
  have hw : 0 ≤ 1-z := by linarith [hz.2]
  have hD : 0 < 1+accumulatedBirth x*(1-z) := by positivity
  have hq0 : 0 ≤ meanRatio x*(1-z)/(1+accumulatedBirth x*(1-z)) := by positivity
  have hq1 : meanRatio x*(1-z)/(1+accumulatedBirth x*(1-z)) ≤ 1 := by
    apply (div_le_one hD).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) hw, hz.1]
  unfold ScalarBackward.candidate
  constructor <;> linarith

noncomputable def endpointWeight : ℕ → ℝ
  | 0 => 1-(33/64)*geometricParameter
  | n+1 => (33/64)*geometricParameter^2*(1-geometricParameter)^n

theorem endpointWeight_nonneg (n : ℕ) : 0 ≤ endpointWeight n := by
  obtain ⟨hl, hu⟩ := geometricParameter_bounds
  cases n with
  | zero => unfold endpointWeight; linarith
  | succ n => unfold endpointWeight; positivity [sub_nonneg.mpr (show geometricParameter ≤ 1 by linarith)]

theorem endpointWeight_pgf (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (fun n => endpointWeight n*z^n)
      (ScalarBackward.candidate meanRatio accumulatedBirth z 0) := by
  obtain ⟨hl, hu⟩ := geometricParameter_bounds
  have hp : 0 ≤ geometricParameter := by linarith
  have hr : 0 ≤ 1-geometricParameter := by linarith
  have hq : (1-geometricParameter)*z < 1 := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hz.2), hz.1]
  have hq0 := mul_nonneg hr hz.1
  have hs := (hasSum_geometric_of_lt_one hq0 hq).mul_left ((33/64)*geometricParameter^2*z)
  have ht : HasSum (fun n => endpointWeight (n+1)*z^(n+1))
      ((33/64)*geometricParameter^2*z*(1-(1-geometricParameter)*z)⁻¹) := by
    convert hs using 1
    ext n
    simp only [endpointWeight, pow_succ, mul_pow]
    ring
  have h := (hasSum_nat_add_iff (f := fun n => endpointWeight n*z^n) 1).mp ht
  simp only [Finset.sum_range_one, endpointWeight, pow_zero, mul_one] at h
  have hid := parameter_birth_identity
  have ha := accumulatedBirth_nonneg 0 (by norm_num)
  have hD : 1+accumulatedBirth 0*(1-z) ≠ 0 := by positivity [sub_nonneg.mpr hz.2]
  have hQ : 1-(1-geometricParameter)*z ≠ 0 := by linarith
  have he : geometricParameter*(1+accumulatedBirth 0*(1-z)) = 1-(1-geometricParameter)*z := by
    nlinarith [congrArg (fun u : ℝ => u*z) hid]
  have hp0 : geometricParameter ≠ 0 := by linarith
  convert h using 1
  unfold ScalarBackward.candidate
  norm_num [meanRatio, den]
  rw [← he]
  have hD2 : 1+(1-z)*accumulatedBirth 0 ≠ 0 := by simpa only [mul_comm] using hD
  field_simp [hD, hD2, hp0]
  nlinarith [he]

end InheritedCellAssay.ScalarRateSource

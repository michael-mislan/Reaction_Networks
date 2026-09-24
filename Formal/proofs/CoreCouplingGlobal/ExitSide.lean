import proofs.CoreCouplingGlobal.ActualExitEnergy

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem continuous_nonzero_negative (f : ℝ → ℝ) (T : ℝ)
    (hf : ContinuousOn f (Icc 0 T)) (hn : ∀ t ∈ Icc 0 T, f t ≠ 0)
    (h0 : f 0 < 0) : ∀ t ∈ Icc 0 T, f t < 0 := by
  intro t ht
  by_contra hbad
  have hc : ContinuousOn f (Icc 0 t) := hf.mono
    (fun _ hu => ⟨hu.1,hu.2.trans ht.2⟩)
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc ht.1 hc ⟨h0.le,le_of_not_gt hbad⟩
  exact hn u ⟨hu.1,hu.2.trans ht.2⟩ hfu

theorem trajectory_B_side_persists (e T : ℝ) (hT : 0 ≤ T)
    (X Y : ℝ → State) (hX : IsPositiveTrajectory e X) (hY : IsPositiveTrajectory e Y)
    (hn : ∀ t ∈ Icc 0 T, (X t).B ≠ (Y t).B) :
    ∀ t ∈ Icc 0 T,
      ((Y t).B < (X t).B ↔ (Y 0).B < (X 0).B) ∧
      ((X t).B < (Y t).B ↔ (X 0).B < (Y 0).B) := by
  have hc : ContinuousOn (fun t => (Y t).B-(X t).B) (Icc 0 T) := by
    intro t ht
    exact ((hY.dB t ht.1).sub (hX.dB t ht.1)).continuousAt.continuousWithinAt
  have hcn : ContinuousOn (fun t => (X t).B-(Y t).B) (Icc 0 T) := by
    intro t ht
    exact ((hX.dB t ht.1).sub (hY.dB t ht.1)).continuousAt.continuousWithinAt
  have hneg := continuous_nonzero_negative _ T hc
    (fun t ht => sub_ne_zero.mpr (Ne.symm (hn t ht)))
  have hpos := continuous_nonzero_negative _ T hcn
    (fun t ht => sub_ne_zero.mpr (hn t ht))
  have hn0 := hn 0 ⟨le_rfl,hT⟩
  intro t ht
  constructor
  · constructor
    · intro hy
      by_contra hbad
      have hx0 : (X 0).B < (Y 0).B := lt_of_le_of_ne (le_of_not_gt hbad) hn0
      have hh := hpos (sub_neg.mpr hx0) t ht
      linarith
    · intro hy
      exact sub_neg.mp (hneg (sub_neg.mpr hy) t ht)
  · constructor
    · intro hx
      by_contra hbad
      have hy0 : (Y 0).B < (X 0).B := lt_of_le_of_ne (le_of_not_gt hbad) (Ne.symm hn0)
      have hh := hneg (sub_neg.mpr hy0) t ht
      linarith
    · intro hx
      exact sub_neg.mp (hpos (sub_neg.mpr hx) t ht)

theorem middle_cone_side_coefficient_pos (e z α : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (hz : z ∈ Icc (19/10:ℝ) (21/10)) (hα : 0 < α) :
    0 < α/(2*localForkSlope e (60/(z+2)) z*(60/(z+2))) := by
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hB := curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hc := local_response_coefficients e 0 (60/(z+2)) z he hu (by norm_num)
    (by norm_num) hB.1 hB.2 hz0 (by linarith [hz.2])
  have hm : 0 < localForkSlope e (60/(z+2)) z := by linarith [hc.2.2.2.2.1]
  positivity

/-- At exit, a sufficiently small reference offset preserves the initial
B departure side relative to the middle equilibrium. -/
theorem cone_exit_initial_side (e z α r θ T : ℝ) (p : SaddleVector)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hα : 0 < α) (hr : 0 < r) (hT : 0 ≤ T) (hθ : θ ≤ 1/2)
    (hθβ : θ ≤ (α/(2*localForkSlope e (60/(z+2)) z*(60/(z+2))))/4)
    (X Y : ℝ → State) (hX : IsPositiveTrajectory e X) (hY : IsPositiveTrajectory e Y)
    (hn : ∀ t ∈ Icc 0 T, (X t).B ≠ (Y t).B)
    (hx : dist (saddleCoordinates e (X T)) p < θ*r)
    (hy : dist (saddleCoordinates e (Y T)) p = r)
    (hq : pairConeValue e z α X Y T ≤ 0) :
    ((Y T).B < p 0 ↔ (Y 0).B < (X 0).B) ∧
    (p 0 < (Y T).B ↔ (X 0).B < (Y 0).B) := by
  let x := saddleCoordinates e (X T)
  let y := saddleCoordinates e (Y T)
  let β := α/(2*localForkSlope e (60/(z+2)) z*(60/(z+2)))
  have hβ : 0 < β := middle_cone_side_coefficient_pos e z α he hu hz hα
  have hhalf : dist x p < r/2 := by
    have hh := mul_le_mul_of_nonneg_right hθ hr.le
    change dist x p < θ*r at hx
    linarith
  have htri := dist_triangle y x p
  rw [hy,dist_comm y x,dist_eq_norm x y] at htri
  have hnorm : r/2 < ‖x-y‖ := by linarith
  have hcoord : |x 0-p 0| ≤ dist x p := norm_le_pi_norm (x-p) 0
  have hb : θ*r ≤ β*r/4 := by
    have hh := mul_le_mul_of_nonneg_right hθβ hr.le
    change θ ≤ β/4 at hθβ
    nlinarith only [hh]
  have hoff : |x 0-p 0| < β*‖x-y‖ := by
    have hh := mul_lt_mul_of_pos_left hnorm hβ
    have hp : 0 < β*r := mul_pos hβ hr
    linarith
  have hs := perturbed_cone_side_transfer e z α he hu hz hα x y p hq hoff
  have hp := trajectory_B_side_persists e T hT X Y hX hY hn T ⟨hT,le_rfl⟩
  exact ⟨hs.1.trans hp.1,hs.2.trans hp.2⟩

end CoreCouplingGlobal

import proofs.RandomViability.BindingUnitGenerator
import proofs.RandomViability.BindingStoppedModel
import proofs.FiniteCopy.UniformizedBounds

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators

def upperUnitPotential (side : Bool) (V : ℝ) (N : Counts) : ℝ :=
  Real.exp ((1/100)*(unitObs side N-(11/10)*V))
def lowerUnitPotential (side : Bool) (V : ℝ) (N : Counts) : ℝ :=
  Real.exp ((-1/100)*(unitObs side N-(9/10)*V))
def resourceSource (V : ℝ) : ℝ := 3000*V*Real.exp (-V/2000+1/50)

theorem literal_upper_foster (side : Bool) (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (htotal : (∑ j,countRate N V eps k r j) ≤ 3000*V) :
    literalGenerator N V eps k r (upperUnitPotential side V) ≤ resourceSource V := by
  by_cases hA : (21/20)*V ≤ unitObs side N
  · unfold upperUnitPotential
    rw [unit_exponential_generator]
    have h := (unit_exponential_tilt side N V eps k r (1/100) hV heps hk hr
      (by norm_num)).trans (upper_moiety_restoring V (unitObs side N) hV.le hA)
    exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h).trans (by
      unfold resourceSource
      positivity)
  · have hsmall : (1/100)*(unitObs side N-(11/10)*V) ≤ -V/2000 := by linarith
    have h := unit_exponential_small_value side N V eps k r (1/100) ((11/10)*V)
      (-V/2000) hV heps hk hr (by norm_num) hsmall
    have hh := mul_le_mul_of_nonneg_left htotal (Real.exp_pos (-V/2000+1/50)).le
    exact h.trans (by simpa only [resourceSource,mul_comm] using hh)

theorem literal_lower_foster (side : Bool) (N : Counts) (V eps k r : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (htotal : (∑ j,countRate N V eps k r j) ≤ 3000*V) :
    literalGenerator N V eps k r (lowerUnitPotential side V) ≤ resourceSource V := by
  by_cases hA : unitObs side N ≤ (19/20)*V
  · unfold lowerUnitPotential
    rw [unit_exponential_generator]
    have h := (unit_exponential_tilt side N V eps k r (-1/100) hV heps hk hr
      (by norm_num)).trans (lower_moiety_restoring V (unitObs side N) hV.le hA)
    exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h).trans (by
      unfold resourceSource
      positivity)
  · have hsmall : (-1/100)*(unitObs side N-(9/10)*V) ≤ -V/2000 := by linarith
    have h := unit_exponential_small_value side N V eps k r (-1/100) ((9/10)*V)
      (-V/2000) hV heps hk hr (by norm_num) hsmall
    have hh := mul_le_mul_of_nonneg_left htotal (Real.exp_pos (-V/2000+1/50)).le
    exact h.trans (by simpa only [resourceSource,mul_comm] using hh)

theorem stopped_generator_inside (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (N : BoxCounts V) (f : Counts → ℝ) (h : resourceGood (boxCounts N) V) :
    (stoppedModel V eps k r hV heps hk hr).generator (fun X => f (boxCounts X)) N =
      literalGenerator (boxCounts N) V eps k r f := by
  simp only [FiniteJumpModel.generator,stoppedModel,stoppedRate,if_pos h,literalGenerator]
  apply Finset.sum_congr rfl
  intro j _
  rw [boxNext_exact V N j h]

theorem stopped_generator_outside (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (N : BoxCounts V) (f : BoxCounts V → ℝ) (h : ¬resourceGood (boxCounts N) V) :
    (stoppedModel V eps k r hV heps hk hr).generator f N = 0 := by
  simp [FiniteJumpModel.generator,stoppedModel,stoppedRate,h]

theorem stopped_upper_foster (side : Bool) (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (N : BoxCounts V) :
    (stoppedModel V eps k r hV heps hk hr).generator
      (fun X => upperUnitPotential side V (boxCounts X)) N ≤ resourceSource V := by
  by_cases h : resourceGood (boxCounts N) V
  · rw [stopped_generator_inside V eps k r hV heps hk hr N _ h]
    apply literal_upper_foster side (boxCounts N) V eps k r hV heps hk hr
    apply total_rate_bound (boxCounts N) V eps k r hV heps heps1 hk hk1 hr hr22
    intro i
    have hi := resource_count_cap (boxCounts N) V h i
    linarith
  · rw [stopped_generator_outside V eps k r hV heps hk hr N _ h]
    unfold resourceSource
    positivity

theorem stopped_lower_foster (side : Bool) (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (N : BoxCounts V) :
    (stoppedModel V eps k r hV heps hk hr).generator
      (fun X => lowerUnitPotential side V (boxCounts X)) N ≤ resourceSource V := by
  by_cases h : resourceGood (boxCounts N) V
  · rw [stopped_generator_inside V eps k r hV heps hk hr N _ h]
    apply literal_lower_foster side (boxCounts N) V eps k r hV heps hk hr
    apply total_rate_bound (boxCounts N) V eps k r hV heps heps1 hk hk1 hr hr22
    intro i
    have hi := resource_count_cap (boxCounts N) V h i
    linarith
  · rw [stopped_generator_outside V eps k r hV heps hk hr N _ h]
    unfold resourceSource
    positivity

end
end RandomViability.Binding

import proofs.StartupMarked.ControlScale
import Mathlib.Analysis.Complex.ExponentialBounds

namespace StartupMarked
open Classical RandomViability MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 50000

theorem retained_control_scalar : 22*Real.exp (-79) < (1/1000 : ℝ) := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 20
  have he : Real.exp (20 : ℝ) = (Real.exp 1)^20 := by norm_num [← Real.exp_nat_mul]
  have hb : (22000 : ℝ) < Real.exp 79 := by
    apply lt_of_lt_of_le _ (Real.exp_le_exp.mpr (by norm_num : (20 : ℝ) ≤ 79))
    rw [he]
    exact (by norm_num : (22000 : ℝ) < (2 : ℝ)^20).trans_le hp
  rw [Real.exp_neg,← div_eq_mul_inv]
  exact (div_lt_iff₀ (Real.exp_pos _)).mpr (by linarith)

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)] [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem retained_controls_uniform (hn : 4 ≤ n) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 1000000000000000000000000 ≤ (V : ℝ))
    (hVn : 10000000000000*(n : ℝ) ≤ V)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 1) (hc : ∀ r q,(cat r q : ℝ) ≤ 16) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 (by linarith) (by norm_num) basal cat N
      {z | ¬retainedControls c V basal cat r z} < ENNReal.ofReal (1/1000 : ℝ) := by
  have hm := retained_jump_margins n V hV hVn
  have hh := retained_controls_failure hn c V (by linarith) basal cat N r hb hc
    (99/800) (99/8000) (99/10000000) (99/4000) (99/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2
  have he := retained_exponents n V (by exact_mod_cast hn) hV hVn
  have hbnd (E : ℝ) (hE : 79 < E) : ENNReal.ofReal (Real.exp (-E)) ≤ ENNReal.ofReal (Real.exp (-79)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hE.le))
  have hu := add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_right (hbnd _ he.1) 2) (mul_le_mul_right (hbnd _ he.2.1) 12))
    (mul_le_mul_right (hbnd _ he.2.2.1) 4)) (mul_le_mul_right (hbnd _ he.2.2.2.1) 2))
    (mul_le_mul_right (hbnd _ he.2.2.2.2) 2)
  apply (hh.trans hu).trans_lt
  have heq : 2*ENNReal.ofReal (Real.exp (-79))+12*ENNReal.ofReal (Real.exp (-79))+
      4*ENNReal.ofReal (Real.exp (-79))+2*ENNReal.ofReal (Real.exp (-79))+
      2*ENNReal.ofReal (Real.exp (-79)) = ENNReal.ofReal (22*Real.exp (-79)) := by
    rw [ENNReal.ofReal_mul (by norm_num),ENNReal.ofReal_ofNat]
    ring
  rw [heq]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr retained_control_scalar

end
end StartupMarked

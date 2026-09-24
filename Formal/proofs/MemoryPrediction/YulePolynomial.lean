import proofs.MemoryPrediction.FiniteBackward

namespace MemoryPrediction
noncomputable section
open FiniteCopy CompositionalMemory

def yuleNext (n : Fin 9) : Fin 9 := if h : n.val < 8 then ⟨n.val+1, by omega⟩ else n
def yuleFinite : FiniteJumpModel (Fin 9) Bool where
  next n e := if e then yuleNext n else n
  rate n e := if e then (n.val : ℝ) else 0
  nonneg n e := by split_ifs <;> positivity

theorem yule_generator (g : Fin 9 → ℝ) (n : Fin 9) :
    yuleFinite.generator g n = (n.val : ℝ)*(g (yuleNext n)-g n) := by
  simp [FiniteJumpModel.generator, yuleFinite]

def yuleCoeff : Fin 8 → Fin 9 → Fin 8 → ℤ := ![
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 2, -1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 3, -3, 1, 0, 0, 0, 0], ![0, 0, 3, -2, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 4, -6, 4, -1, 0, 0, 0], ![0, 0, 6, -8, 3, 0, 0, 0], ![0, 0, 0, 4, -3, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 5, -10, 10, -5, 1, 0, 0], ![0, 0, 10, -20, 15, -4, 0, 0], ![0, 0, 0, 10, -15, 6, 0, 0], ![0, 0, 0, 0, 5, -4, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 6, -15, 20, -15, 6, -1, 0], ![0, 0, 15, -40, 45, -24, 5, 0], ![0, 0, 0, 20, -45, 36, -10, 0], ![0, 0, 0, 0, 15, -24, 10, 0], ![0, 0, 0, 0, 0, 6, -5, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0]],
  ![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 7, -21, 35, -35, 21, -7, 1], ![0, 0, 21, -70, 105, -84, 35, -6], ![0, 0, 0, 35, -105, 126, -70, 15], ![0, 0, 0, 0, 35, -84, 70, -20], ![0, 0, 0, 0, 0, 21, -35, 15], ![0, 0, 0, 0, 0, 0, 7, -6], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0]]
]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem yule_coefficient_identity : ∀ (k : Fin 8) (n : Fin 9) (j : Fin 8),
    -(j.val : ℤ)*yuleCoeff k n j =
      (n.val : ℤ)*(yuleCoeff k (yuleNext n) j-yuleCoeff k n j) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem yule_coefficient_initial : ∀ (k : Fin 8) (n : Fin 9),
    (∑ j, yuleCoeff k n j) = if n.val ≤ k.val then 1 else 0 := by decide

def yuleValue (k : Fin 8) (t : ℝ) (n : Fin 9) : ℝ :=
  ∑ j : Fin 8, (yuleCoeff k n j : ℝ)*Real.exp (-(j.val : ℝ)*t)

theorem yule_value_deriv (k : Fin 8) (t : ℝ) (n : Fin 9) :
    HasDerivAt (fun u => yuleValue k u n) (yuleFinite.generator (yuleValue k t) n) t := by
  have hd (j : Fin 8) : HasDerivAt
      (fun u : ℝ => (yuleCoeff k n j : ℝ)*Real.exp (-(j.val : ℝ)*u))
      ((-(j.val : ℝ)*(yuleCoeff k n j : ℝ))*Real.exp (-(j.val : ℝ)*t)) t := by
    convert ((((hasDerivAt_id t).const_mul (-(j.val : ℝ))).exp).const_mul
      (yuleCoeff k n j : ℝ)) using 1
    simp only [id_eq]
    ring
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
  convert h using 1
  rw [yule_generator]
  unfold yuleValue
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hc : -(j.val : ℝ)*(yuleCoeff k n j : ℝ) =
      (n.val : ℝ)*((yuleCoeff k (yuleNext n) j : ℝ)-(yuleCoeff k n j : ℝ)) := by
    exact_mod_cast yule_coefficient_identity k n j
  rw [hc]
  ring

def yulePayoff (k : Fin 8) (n : Fin 9) : ℝ := if n.val ≤ k.val then 1 else 0

theorem yule_value_initial (k : Fin 8) : yuleValue k 0 = yulePayoff k := by
  funext n
  simp only [yuleValue,mul_zero,Real.exp_zero,mul_one]
  unfold yulePayoff
  have h := yule_coefficient_initial k n
  exact_mod_cast h

theorem yule_finite_exact (k : Fin 8) (T : NNReal) (n : Fin 9) :
    finiteTimeExpectation yuleFinite T (yulePayoff k) n = yuleValue k T n := by
  rw [← yule_value_initial k]
  exact finite_backward_identity yuleFinite (yuleValue k) (yule_value_deriv k) T n

def yuleHorizon : NNReal := ⟨Real.log 2, by positivity⟩
def yuleAtHalf (k : Fin 8) (n : Fin 9) : ℝ :=
  ∑ j : Fin 8, (yuleCoeff k n j : ℝ)*(1/2 : ℝ)^j.val

theorem yule_value_half (k : Fin 8) (n : Fin 9) :
    yuleValue k yuleHorizon n = yuleAtHalf k n := by
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change Real.exp (-(j.val : ℝ)*Real.log 2) = _
  rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp [inv_pow]

end
end MemoryPrediction

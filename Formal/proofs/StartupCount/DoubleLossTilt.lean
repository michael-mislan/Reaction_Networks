import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace StartupCount
open scoped BigOperators

/-- A two-copy loss is charged twice its copy flux, not treated as a unit
death. Helpful jumps make a nonpositive contribution to the tilt. -/
theorem double_loss_tilt (s : ℝ) (hs : 0 ≤ s) (K L : ℕ) (hdown : K ≤ L+2) :
    Real.exp (s*((K : ℝ)-L))-1 ≤
      (Real.exp (2*s)-1)/2 * max 0 ((K : ℝ)-L) := by
  by_cases hKL : K ≤ L
  · have hreal : (K : ℝ) ≤ L := by exact_mod_cast hKL
    have hd : (K : ℝ)-L ≤ 0 := sub_nonpos.mpr hreal
    rw [max_eq_left hd,mul_zero]
    exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hs hd))
  · have hh : K = L+1 ∨ K = L+2 := by omega
    rcases hh with rfl | rfl
    · have he : Real.exp (2*s) = Real.exp s*Real.exp s := by rw [two_mul,Real.exp_add]
      norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_left,mul_one,
        max_eq_right (show (0:ℝ) ≤ 1 by norm_num)]
      rw [he]
      nlinarith [sq_nonneg (Real.exp s-1)]
    · norm_num only [Nat.cast_add,Nat.cast_ofNat,add_sub_cancel_left,
        max_eq_right (show (0:ℝ) ≤ 2 by norm_num)]
      rw [mul_comm s 2]
      linarith

/-- Finite marked-generator estimate. The immigration channel is an actual
retained +1 channel; all other births stay present and are discarded only
from this upper bound. No birth-death domination is assumed. -/
theorem immigration_double_loss_generator {J : Type*} [Fintype J] [DecidableEq J]
    (rate : J → ℝ) (hRate : ∀ j,0 ≤ rate j) (next : J → ℕ) (K : ℕ)
    (selected : J) (hSelected : next selected = K+1)
    (iota delta s : ℝ) (hs : 0 ≤ s) (hIota : iota ≤ rate selected)
    (hDown : ∀ j,K ≤ next j+2)
    (hLoss : (∑ j,rate j*max 0 ((K : ℝ)-next j)) ≤ delta*K) :
    (∑ j,rate j*(Real.exp (s*((K : ℝ)-next j))-1)) ≤
      -iota*(1-Real.exp (-s)) + delta/2*(Real.exp (2*s)-1)*K := by
  let A := (Real.exp (2*s)-1)/2
  let B := 1-Real.exp (-s)
  have hA : 0 ≤ A := by
    have hh := Real.one_le_exp_iff.mpr (show 0 ≤ 2*s by linarith)
    dsimp [A]
    linarith
  have hB : 0 ≤ B := by
    have hh := Real.exp_le_one_iff.mpr (show -s ≤ 0 by linarith)
    dsimp [B]
    linarith
  have hpoint (j : J) : rate j*(Real.exp (s*((K : ℝ)-next j))-1) ≤
      rate j*(A*max 0 ((K : ℝ)-next j) - if j = selected then B else 0) := by
    by_cases hj : j = selected
    · subst j
      rw [hSelected,if_pos rfl]
      have hd : (K : ℝ)-(K+1 : ℕ) = -1 := by push_cast; ring
      rw [hd]
      norm_num only [max_eq_left (show (-1:ℝ) ≤ 0 by norm_num),mul_zero,zero_sub,mul_neg_one]
      dsimp [B]
      ring_nf
      exact le_rfl
    · rw [if_neg hj,sub_zero]
      exact mul_le_mul_of_nonneg_left (double_loss_tilt s hs K (next j) (hDown j)) (hRate j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => hpoint j)
  have he : (∑ j,rate j*(A*max 0 ((K : ℝ)-next j) - if j = selected then B else 0)) =
      A*(∑ j,rate j*max 0 ((K : ℝ)-next j)) - rate selected*B := by
    simp [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_ite,mul_comm,mul_assoc]
  rw [he] at hsum
  have hl := mul_le_mul_of_nonneg_left hLoss hA
  have hi := mul_le_mul_of_nonneg_right hIota hB
  dsimp [A,B] at hsum hl hi
  nlinarith only [hsum,hl,hi]

end StartupCount

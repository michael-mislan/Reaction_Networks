import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-! Uniform finite-inventory certificate soundness. This file does not assume
an aggregated resource inequality; it derives one from every chemical floor
and auxiliary equality. Source data and the evaluated cost remain separate. -/
namespace StoredRedCells.FiniteCertificate
noncomputable section
open Finset

/-- Sparse columns retain duplicate entries by summation. This identity is the
source-data bridge from term lists to species-indexed matrix columns. -/
theorem weighted_sparse_column {I : Type*} [Fintype I] [DecidableEq I]
    (terms : List (I × ℝ)) (w : I → ℝ) :
    (∑ i, w i * (terms.map (fun p => if p.1 = i then p.2 else 0)).sum) =
      (terms.map (fun p => w p.1 * p.2)).sum := by
  induction terms with
  | nil => simp
  | cons p terms ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [ih]
    simp

theorem interval_term (d L U v T : ℝ) (hT : 0 ≤ T)
    (hL : L*T ≤ v) (hU : v ≤ U*T) :
    d*v ≤ max (d*L) (d*U)*T := by
  by_cases hd : 0 ≤ d
  · calc
      d*v ≤ d*(U*T) := mul_le_mul_of_nonneg_left hU hd
      _ = (d*U)*T := by ring
      _ ≤ max (d*L) (d*U)*T := mul_le_mul_of_nonneg_right (le_max_right _ _) hT
  · calc
      d*v ≤ d*(L*T) := mul_le_mul_of_nonpos_left hL (le_of_not_ge hd)
      _ = (d*L)*T := by ring
      _ ≤ max (d*L) (d*U)*T := mul_le_mul_of_nonneg_right (le_max_left _ _) hT

/-- Natural-number source indices are checked against the finite species set. -/
theorem weighted_nat_column {n : Nat} (terms : List (Nat × ℝ)) (w : Nat → ℝ)
    (hidx : ∀ p ∈ terms, p.1 < n) :
    (∑ i : Fin n, w i.val *
      (terms.map (fun p => if p.1 = i.val then p.2 else 0)).sum) =
      (terms.map (fun p => w p.1 * p.2)).sum := by
  induction terms with
  | nil => simp
  | cons p terms ih =>
    have hp : p.1 < n := hidx p (by simp)
    have ht : ∀ q ∈ terms, q.1 < n := fun q hq => hidx q (by simp [hq])
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [ih ht]
    have heq (i : Fin n) : p.1 = i.val ↔ (⟨p.1, hp⟩ : Fin n) = i := by
      constructor
      · intro h
        exact Fin.ext h
      · intro h
        exact congrArg Fin.val h
    simp_rw [heq]
    simp

theorem weighted_sum_swap {I J : Type*} [Fintype I] [Fintype J]
    (w : I → ℝ) (N : I → J → ℝ) (v : J → ℝ) :
    (∑ j, (∑ i, w i*N i j)*v j) = ∑ i, w i*(∑ j, N i j*v j) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem inventory_bound {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]
    (N : I → J → ℝ) (B : A → J → ℝ) (w : I → ℝ) (y : A → ℝ)
    (c d L U v : J → ℝ) (x0 ell : I → ℝ) (T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hT : 0 ≤ T)
    (hfloor : ∀ i, w i ≠ 0 → ell i ≤ x0 i + ∑ j, N i j*v j)
    (haux : ∀ a, y a ≠ 0 → ∑ j, B a j*v j=0)
    (hL : ∀ j, L j*T ≤ v j) (hU : ∀ j, v j ≤ U j*T)
    (hcol : ∀ j, c j = -(∑ i, w i*N i j)+(∑ a, y a*B a j)+d j) :
    (∑ j, c j*v j) ≤ (∑ i, w i*(x0 i-ell i))+
      (∑ j, max (d j*L j) (d j*U j))*T := by
  have hc : -(∑ i, w i*(∑ j, N i j*v j)) ≤ ∑ i, w i*(x0 i-ell i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    by_cases hz : w i = 0
    · simp [hz]
    · have hh := mul_le_mul_of_nonneg_left (hfloor i hz) (hw i)
      nlinarith
  have ha : (∑ a, y a*(∑ j, B a j*v j))=0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases hz : y a = 0
    · simp [hz]
    · rw [haux a hz, mul_zero]
  have hd : (∑ j, d j*v j) ≤ (∑ j, max (d j*L j) (d j*U j))*T := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => interval_term _ _ _ _ _ hT (hL j) (hU j))
  have hid : (∑ j, c j*v j) = -(∑ i, w i*(∑ j, N i j*v j))+
      (∑ a, y a*(∑ j, B a j*v j))+(∑ j, d j*v j) := by
    simp_rw [hcol, add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [weighted_sum_swap, weighted_sum_swap]
  rw [hid, ha]
  linarith

/-- Add nonnegative supply charges to the objective, then retain their negative
extent contributions explicitly. No reaction direction is forbidden. -/
theorem inventory_with_reverse_supplies
    {I J A : Type*} [Fintype I] [Fintype J] [Fintype A]
    (N : I → J → ℝ) (B : A → J → ℝ) (w : I → ℝ) (y : A → ℝ)
    (c a d L U v : J → ℝ) (x0 ell : I → ℝ) (T : ℝ)
    (hw : ∀ i, 0 ≤ w i) (ha : ∀ j, 0 ≤ a j) (hT : 0 ≤ T)
    (hfloor : ∀ i, w i ≠ 0 → ell i ≤ x0 i + ∑ j, N i j*v j)
    (haux : ∀ i, y i ≠ 0 → ∑ j, B i j*v j = 0)
    (hL : ∀ j, L j*T ≤ v j) (hU : ∀ j, v j ≤ U j*T)
    (hcol : ∀ j, c j+a j =
      -(∑ i, w i*N i j)+(∑ i, y i*B i j)+d j) :
    (∑ j, c j*v j) ≤ (∑ i, w i*(x0 i-ell i)) +
      (∑ j, max (d j*L j) (d j*U j))*T +
      (∑ j, a j*max (-v j) 0) := by
  have h := inventory_bound N B w y (fun j => c j+a j) d L U v x0 ell T
    hw hT hfloor haux hL hU hcol
  have hid : (∑ j, (c j+a j)*v j) = (∑ j, c j*v j)+(∑ j, a j*v j) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hid] at h
  have hs : -(∑ j, a j*v j) ≤ ∑ j, a j*max (-v j) 0 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    calc
      -(a j*v j) = a j*(-v j) := by ring
      _ ≤ a j*max (-v j) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (ha j)
  linarith only [h, hs]

end
end StoredRedCells.FiniteCertificate

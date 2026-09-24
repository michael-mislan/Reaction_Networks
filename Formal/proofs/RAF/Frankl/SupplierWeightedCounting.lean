import proofs.RAF.Frankl.LocallyRankedSupplierCore

namespace RAF.Frankl
open scoped BigOperators

/-- Bounded within-fibre weight variation converts half occupancy to 1/(1+k). -/
theorem bounded_weight_average {X : Type*} (F : Finset X) (x w : X → ℝ)
    (n lo k : ℝ) (hlo : 0 ≤ lo) (hk : 0 ≤ k)
    (hx : ∀ a ∈ F, 0 ≤ x a ∧ x a ≤ n)
    (hw : ∀ a ∈ F, lo ≤ w a ∧ w a ≤ k*lo)
    (havg : n * F.card ≤ 2 * ∑ a ∈ F, x a) :
    n * (∑ a ∈ F, w a) ≤ (1+k) * ∑ a ∈ F, w a*x a := by
  have h1 : (∑ a ∈ F, w a*(n-x a)) ≤ k*lo * ∑ a ∈ F, (n-x a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (hw a ha).2 (sub_nonneg.mpr (hx a ha).2)
  have h2 : (∑ a ∈ F, (n-x a)) ≤ ∑ a ∈ F, x a := by
    rw [Finset.sum_sub_distrib,Finset.sum_const]
    simp only [nsmul_eq_mul]
    nlinarith
  have h3 : lo * (∑ a ∈ F, x a) ≤ ∑ a ∈ F, w a*x a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_right (hw a ha).1 (hx a ha).1
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hk hlo)
  have h5 := mul_le_mul_of_nonneg_left h3 hk
  have he : (∑ a ∈ F, w a*(n-x a)) = n*(∑ a ∈ F, w a) - ∑ a ∈ F, w a*x a := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    ring
  rw [he] at h1
  nlinarith

theorem sum_over_exterior {X V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset X) (tag : X → V) (f : X → ℝ) :
    (∑ t : V, ∑ a ∈ F.filter (fun a => tag a=t), f a) = ∑ a ∈ F, f a := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem weighted_fibre_aggregation {X V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset X) (tag : X → V) (x w : X → ℝ) (n k : ℝ) (lo : V → ℝ)
    (hlo : ∀ t, 0 ≤ lo t) (hk : 0 ≤ k)
    (hx : ∀ a ∈ F, 0 ≤ x a ∧ x a ≤ n)
    (hw : ∀ a ∈ F, lo (tag a) ≤ w a ∧ w a ≤ k*lo (tag a))
    (havg : ∀ t, n * (F.filter (fun a => tag a=t)).card ≤
      2 * ∑ a ∈ F.filter (fun a => tag a=t), x a) :
    n * (∑ a ∈ F, w a) ≤ (1+k)*∑ a ∈ F, w a*x a := by
  classical
  have h : ∀ t, n*(∑ a ∈ F.filter (fun a => tag a=t), w a) ≤
      (1+k)*∑ a ∈ F.filter (fun a => tag a=t), w a*x a := by
    intro t
    apply bounded_weight_average _ x w n (lo t) k (hlo t) hk
    · intro a ha
      exact hx a (Finset.mem_filter.mp ha).1
    · intro a ha
      have ht := (Finset.mem_filter.mp ha).2
      simpa only [ht] using hw a (Finset.mem_filter.mp ha).1
    · exact havg t
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => h t)
  simpa only [← Finset.mul_sum,sum_over_exterior] using hh

theorem weighted_coordinate_witness {X R : Type*} [Fintype R] [Nonempty R] [DecidableEq R]
    (F : Finset X) (left : X → Finset R) (w : X → ℝ) (k : ℝ)
    (h : (Fintype.card R : ℝ)*(∑ a ∈ F, w a) ≤
      (1+k)*∑ a ∈ F, w a*(left a).card) :
    ∃ r : R, (∑ a ∈ F, w a) ≤ (1+k)*∑ a ∈ F.filter (fun a => r ∈ left a), w a := by
  classical
  have hi : (∑ a ∈ F, w a*(left a).card) =
      ∑ r : R, ∑ a ∈ F.filter (fun a => r ∈ left a), w a := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp [mul_comm]
  rw [hi] at h
  by_contra hn
  push Not at hn
  have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun r _ => hn r)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  rw [← Finset.mul_sum] at hh
  linarith

end RAF.Frankl

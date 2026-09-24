import Mathlib

namespace CoreCouplingGlobal
open Set Filter Topology

/-- A scalar trajectory cannot cross a ceiling when its derivative is nonpositive above it. -/
theorem scalar_upper_barrier (y v : ℝ → ℝ) (M : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (h0 : y 0 ≤ M) (hv : ∀ t, 0 ≤ t → M ≤ y t → v t ≤ 0) :
    ∀ t, 0 ≤ t → y t ≤ M := by
  intro t ht
  by_contra hn
  have hlarge : M < y t := lt_of_not_ge hn
  let ε := (y t-M)/(2*(t+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hB : ∀ x : ℝ, HasDerivAt (fun s : ℝ => M+ε*(s+1)) ε x := by
    intro x
    convert (((hasDerivAt_id x).add_const 1).const_mul ε).const_add M using 1
    ring
  have hb := image_le_of_liminf_slope_right_lt_deriv_boundary
    (fun s hs => (hd s hs.1).continuousAt.continuousWithinAt)
    (fun s hs _ hr => (hd s hs.1).hasDerivWithinAt.liminf_right_slope_le hr)
    (show y 0 ≤ M+ε*(0+1) by linarith) hB
    (fun s hs heq => by
      have hs0 : 0 ≤ s := hs.1
      have hMs : M ≤ y s := by
        have hp : 0 ≤ ε*(s+1) := by positivity
        linarith
      have hh := hv s hs0 hMs
      linarith)
    (show t ∈ Icc 0 t from ⟨ht,le_rfl⟩)
  have heq : ε*(t+1) = (y t-M)/2 := by
    dsimp [ε]
    field_simp
  linarith

theorem scalar_lower_barrier (y v : ℝ → ℝ) (M : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (h0 : M ≤ y 0) (hv : ∀ t, 0 ≤ t → y t ≤ M → 0 ≤ v t) :
    ∀ t, 0 ≤ t → M ≤ y t := by
  have hh := scalar_upper_barrier (fun t => -y t) (fun t => -v t) (-M)
    (fun t ht => (hd t ht).neg) (by linarith)
    (fun t ht hh => by have h := hv t ht (by linarith); linarith)
  intro t ht
  have h := hh t ht
  linarith

theorem positive_of_linear_lower (y v : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt y (v t) t)
    (h0 : 0 < y 0) (hv : ∀ t, 0 ≤ t → -L*y t ≤ v t) :
    ∀ t, 0 ≤ t → 0 < y t := by
  have hdw : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.exp (L*s)*y s)
      (Real.exp (L*t)*(L*y t+v t)) t := by
    intro t ht
    convert (((hasDerivAt_id t).const_mul L).exp).mul (hd t ht) using 1
    dsimp
    ring
  have hm : MonotoneOn (fun t => Real.exp (L*t)*y t) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t ht => (hdw t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdw t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => mul_nonneg (Real.exp_pos _).le (by have hh := hv t (interior_subset ht); linarith))
  intro t ht
  have hh := hm (show (0:ℝ) ∈ Ici 0 by simp) (show t ∈ Ici 0 from ht) ht
  simp only [mul_zero,Real.exp_zero,one_mul] at hh
  have hp : 0 < Real.exp (L*t)*y t := lt_of_lt_of_le h0 hh
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).1 hp

end CoreCouplingGlobal

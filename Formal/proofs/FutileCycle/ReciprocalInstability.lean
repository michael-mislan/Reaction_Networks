import Mathlib

namespace FutileCycle
open Polynomial

theorem re_multiset_sum (s : Multiset ℂ) : s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- A zero logarithmic derivative at zero is incompatible with all roots
in the closed left half-plane unless their real-part sum vanishes. -/
theorem exists_rhp_root_of_reciprocal_sum (p : ℂ[X])
    (hp : p.eval 0 ≠ 0) (hd : p.derivative.eval 0 = 0)
    (hs : p.roots.sum.re ≠ 0) : ∃ z, p.IsRoot z ∧ 0 < z.re := by
  classical
  by_contra h
  push Not at h
  have hroot : ∀ z ∈ p.roots, z.re ≤ 0 := by
    intro z hz
    exact h z ((mem_roots (by intro he; simp [he] at hp)).mp hz)
  have hsum := (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hp
  rw [hd, zero_div] at hsum
  have hreal : (p.roots.map (fun z => (1 / (0 - z) : ℂ).re)).sum = 0 := by
    have hh := congrArg Complex.re hsum.symm
    simpa only [re_multiset_sum, Multiset.map_map, Function.comp_def, Complex.zero_re] using hh
  have hn : ∀ x ∈ p.roots.map (fun z => (1 / (0 - z) : ℂ).re), 0 ≤ x := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    simp only [zero_sub, one_div, inv_neg, Complex.neg_re, Complex.inv_re]
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (hroot z hz) (Complex.normSq_nonneg z))
  have hall := Multiset.all_zero_of_le_zero_le_of_sum_eq_zero hn hreal
  have hzre : ∀ z ∈ p.roots, z.re = 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro he
      subst z
      exact hp ((mem_roots (by intro he; simp [he] at hp)).mp hz)
    have he := hall _ (Multiset.mem_map.mpr ⟨z,hz,rfl⟩)
    simp only [zero_sub, one_div, inv_neg, Complex.neg_re, Complex.inv_re,
      neg_eq_zero] at he
    exact (div_eq_zero_iff).mp he |>.resolve_right (by simpa using hz0)
  apply hs
  have hh : (p.roots.map Complex.re).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Multiset.mem_map.mp hx
    exact hzre z hz
  rwa [re_multiset_sum]

end FutileCycle

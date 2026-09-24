import Mathlib

namespace FutileCycle

theorem norm_lt_of_amplifier (a u v : ℂ) (ha : 1 < a.re) (hu : u ≠ 0)
    (he : a*u=v) : ‖u‖ < ‖v‖ := by
  calc
    ‖u‖ = 1*‖u‖ := by ring
    _ < ‖a‖*‖u‖ := mul_lt_mul_of_pos_right
      (lt_of_lt_of_le ha (Complex.re_le_norm a)) (norm_pos_iff.mpr hu)
    _ = ‖v‖ := by rw [← norm_mul, he]

/-- Every proper supported restriction of a directed cycle with one leaf
two-cycle has no RHP eigenpair when each diagonal resolvent has real part >1.
The hypotheses are the coordinate equations, including zeros at omitted rows. -/
theorem flower_restriction_zero (n : ℕ) (u : Fin (n+1) → ℂ) (v : ℂ)
    (p : Fin (n+1) → Prop) (q : Prop)
    (a : Fin (n+1) → ℂ) (b : ℂ)
    (ha : ∀ i, 1 < (a i).re) (hb : 1 < b.re)
    (hzero : ∀ i, ¬p i → u i = 0) (hvzero : ¬q → v=0)
    (hstep : ∀ i : Fin n, p i.succ → a i.succ * u i.succ = u i.castSucc)
    (hleaf : q → b*v=u 0)
    (hhub : p 0 → a 0*u 0=u (Fin.last n)+v)
    (hproper : (∃ i, ¬p i) ∨ ¬q) : (∀ i, u i=0) ∧ v=0 := by
  classical
  have hnorm : ∀ i : Fin n, ‖u i.succ‖ ≤ ‖u i.castSucc‖ := by
    intro i
    by_cases hp : p i.succ
    · by_cases hu : u i.succ=0
      · simp [hu]
      · exact (norm_lt_of_amplifier _ _ _ (ha _) hu (hstep i hp)).le
    · simp [hzero _ hp]
  have hanti : Antitone (fun i => ‖u i‖) := Fin.antitone_iff_succ_le.mpr hnorm
  have hleafnorm : ‖v‖ ≤ ‖u 0‖ := by
    by_cases hq : q
    · by_cases hv : v=0
      · simp [hv]
      · exact (norm_lt_of_amplifier _ _ _ hb hv (hleaf hq)).le
    · simp [hvzero hq]
  have hhubzero : u 0=0 := by
    by_contra hu
    have hp0 : p 0 := by by_contra hh; exact hu (hzero _ hh)
    have hstrict := norm_lt_of_amplifier _ _ _ (ha 0) hu (hhub hp0)
    rcases hproper with ⟨i,hi⟩ | hq
    · have hend : u (Fin.last n)=0 := by
        have hle := hanti (Fin.le_last i)
        dsimp only at hle
        rw [hzero i hi, norm_zero] at hle
        exact norm_le_zero_iff.mp hle
      rw [hend, zero_add] at hstrict
      exact (not_lt_of_ge hleafnorm) hstrict
    · rw [hvzero hq, add_zero] at hstrict
      exact (not_lt_of_ge (hanti (Fin.zero_le _))) hstrict
  constructor
  · intro i
    have hh := hanti (Fin.zero_le i)
    dsimp only at hh
    rw [hhubzero, norm_zero] at hh
    exact norm_le_zero_iff.mp hh
  · rw [hhubzero, norm_zero] at hleafnorm
    exact norm_le_zero_iff.mp hleafnorm

end FutileCycle

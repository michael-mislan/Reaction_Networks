import proofs.DStability5x5.Robustness
import proofs.DStability5x5.Separation
import proofs.DStability5x5.FiveByFive

/-!
# The boundary of the D-stable set (Corollary A2(c) and the separation dichotomy)

* `not_surjective_iff_tangency`: at a point `d`, the real derivative of `contactDet A` fails to be
  surjective (rank `[∇Re; ∇Im] ≤ 1`) iff the tangency equations of branch (c) hold for some real `t`.
* `closure_dichotomy`: a Hurwitz matrix `A₀` in the closure of the D-stable set is either
  - D-stable, with no positive contact at all, and then `κ`-stable on a neighbourhood for every
    `κ` (*separation-protected*: `κ*(A) → ∞` as `A → A₀`); or
  - not D-stable, with at least one positive contact, and **every** positive contact tangential
    (a real solution of the tangency system (c)).
  In particular the Hurwitz part of the frontier of the D-stable set splits into escape points
  (belonging to the set) and tangential points (outside it).
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- Singular contacts are exactly the solutions of the tangency system (c). -/
theorem not_surjective_iff_tangency (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    ¬ Function.Surjective (fderiv ℝ (contactDet A) d) ↔
      ∃ t : ℝ, ∀ i, (1 - t ^ 2) * (partialPoly A d i).re + 2 * t * (partialPoly A d i).im = 0 := by
  rw [regular_iff_rank]
  push Not
  constructor
  · intro h
    by_cases hall : ∀ i, (partialPoly A d i).re = 0 ∧ (partialPoly A d i).im = 0
    · refine ⟨0, fun i => ?_⟩
      rw [(hall i).1, (hall i).2]
      ring
    · push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hpq : (partialPoly A d i₀).im ≠ 0 ∨ -(partialPoly A d i₀).re ≠ 0 := by
        by_cases hre : (partialPoly A d i₀).re = 0
        · exact Or.inl (hi₀ hre)
        · exact Or.inr (neg_ne_zero.mpr hre)
      refine ⟨tpar (partialPoly A d i₀).im (-(partialPoly A d i₀).re), fun i => ?_⟩
      apply tpar_spec _ _ _ _ hpq
      have := h i₀ i
      linear_combination -this
  · rintro ⟨t, ht⟩ i j
    have hi := ht i
    have hj := ht j
    have h1 : ((partialPoly A d i).re * (partialPoly A d j).im -
        (partialPoly A d j).re * (partialPoly A d i).im) * (1 - t ^ 2) = 0 := by
      linear_combination (partialPoly A d j).im * hi - (partialPoly A d i).im * hj
    have h2 : ((partialPoly A d i).re * (partialPoly A d j).im -
        (partialPoly A d j).re * (partialPoly A d i).im) * (2 * t) = 0 := by
      linear_combination -(partialPoly A d j).re * hi + (partialPoly A d i).re * hj
    by_cases ht0 : t = 0
    · rw [ht0] at h1
      simpa using h1
    · have h2t : (2 * t) ≠ 0 := mul_ne_zero two_ne_zero ht0
      exact (mul_eq_zero.mp h2).resolve_right h2t

/-- **Boundary dichotomy.** -/
theorem closure_dichotomy {A₀ : Matrix (Fin n) (Fin n) ℝ} (hH : HurwitzStable A₀)
    (hcl : A₀ ∈ closure {A : Matrix (Fin n) (Fin n) ℝ | DStable A}) :
    (DStable A₀ ∧ (∀ d : Fin n → ℝ, (∀ i, 0 < d i) → contactDet A₀ d ≠ 0) ∧
        ∀ κ : ℝ, 1 ≤ κ → ∀ᶠ A in 𝓝 A₀, KStable κ A) ∨
    (¬ DStable A₀ ∧ (∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ contactDet A₀ d = 0) ∧
        ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → contactDet A₀ d = 0 →
          ∃ t : ℝ, ∀ i, (1 - t ^ 2) * (partialPoly A₀ d i).re +
            2 * t * (partialPoly A₀ d i).im = 0) := by
  by_cases hD : DStable A₀
  · left
    refine ⟨hD, fun d hd hc => ?_, fun κ hκ => eventually_kStable_of_dStable hD hκ⟩
    obtain ⟨v, hv⟩ := (contact_iff_eigenpair A₀ d).mp hc
    have h := hD d hd Complex.I v hv
    simp at h
  · right
    refine ⟨hD, ?_, fun d hd hc => ?_⟩
    · have h := (dStable_iff_morse A₀).not.mp hD
      push Not at h
      obtain ⟨d, hd, hc, -⟩ := h hH
      exact ⟨d, hd, hc⟩
    · have hnr := not_regular_of_mem_closure A₀ hcl d
      have hns : ¬ Function.Surjective (fderiv ℝ (contactDet A₀) d) := fun hs => hnr ⟨hd, hc, hs⟩
      exact (not_surjective_iff_tangency A₀ d).mp hns

end DStability5x5

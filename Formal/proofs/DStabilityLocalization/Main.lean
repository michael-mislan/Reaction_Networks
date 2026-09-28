import proofs.DStabilityLocalization.Sharpness
import proofs.DStabilityLocalization.MarginalGap
import proofs.DStabilityLocalization.LumpingNeeded

/-!
# Root theorems

* `spectral_localization`: every eigenvalue in the closed right half-plane of a positive scaling
  of a star is the same eigenvalue of a positive scaling of one of its boundary systems (at most
  one synchronized group per channel).  No hypothesis on the core.
* `dUnstable_of_boundary` (module `Lifting`): strict growth of a boundary system lifts to the
  star.
* `dStable_of_boundary`: if every boundary system is D-stable, the star is D-stable.
* `dNonUnstable_iff`: the star is D-semistable iff every boundary system is.
* `sharpness`: for every number of channels `k = m + 2` there is a star that is not D-stable
  while every boundary system with fewer than `k` synchronized groups is D-stable.
* `marginal_gap` (module `MarginalGap`): the criterion is not an equivalence.
* `lumping_needed` (module `LumpingNeeded`): synchronized groups of two pieces are needed.
* `localization_and_sharpness`: the conjunction, stated monomorphically (root declaration).
-/

set_option linter.unusedSectionVars false

noncomputable section
open Complex

namespace DStabilityLocalization
open DUnstableCores

/-- **Spectral localization.** -/
theorem spectral_localization {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype C] [DecidableEq C] (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ) (hr : ∀ p, r p ≠ 0) (d : ι ⊕ κ → ℝ) (hd : ∀ a, 0 < d a)
    (z : ℂ) (hre : 0 ≤ z.re) (y : ι ⊕ κ → ℂ)
    (hy : HasEigenpair (rightScale (star B u v ch r) d) z y) :
    ∃ σ : κ → Role, ∃ d' : ι ⊕ C → ℝ, (∀ a, 0 < d' a) ∧ ∃ y',
      HasEigenpair (rightScale (bdSystem B u v ch r σ) d') z y' := by
  by_cases him : z.im = 0
  · rcases hre.lt_or_eq with hpos | hzero
    · obtain ⟨σ, -, d', hd', -, y', hy'⟩ := localization_real B u v ch r d hd hpos him y hy
      exact ⟨σ, d', hd', y', hy'⟩
    · have hz : z = 0 := Complex.ext (by simp [← hzero]) (by simp [him])
      subst hz
      obtain ⟨d', hd', -, y', hy'⟩ := zero_eigen_static B u v ch r d hd y hy
      exact ⟨fun _ => Role.F, d', hd', y', hy'⟩
  · exact localization_nonreal B u v ch r hr d hd hre him y hy

/-- **Criterion.** If every boundary system is D-stable, the star is D-stable. -/
theorem dStable_of_boundary {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype C] [DecidableEq C] (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ) (hr : ∀ p, r p ≠ 0)
    (hbd : ∀ σ : κ → Role, DStable (bdSystem B u v ch r σ)) : DStable (star B u v ch r) := by
  intro d hd z y hy
  by_contra hnot
  have hre : 0 ≤ z.re := not_lt.mp hnot
  obtain ⟨σ, d', hd', y', hy'⟩ := spectral_localization B u v ch r hr d hd z hre y hy
  have := hbd σ d' hd' z y' hy'
  linarith

/-- **Strict growth localizes exactly.** -/
theorem dUnstable_iff {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype C] [DecidableEq C] (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ) (hr : ∀ p, r p ≠ 0) :
    DUnstable (star B u v ch r) ↔ ∃ σ : κ → Role, DUnstable (bdSystem B u v ch r σ) := by
  constructor
  · rintro ⟨d, hd, z, y, hz, hy⟩
    obtain ⟨σ, d', hd', y', hy'⟩ := spectral_localization B u v ch r hr d hd z hz.le y hy
    exact ⟨σ, d', hd', z, y', hz, hy'⟩
  · rintro ⟨σ, hσ⟩
    exact dUnstable_of_boundary B u v ch r σ hσ

/-- **D-semistability localizes exactly.** -/
theorem dNonUnstable_iff {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype C] [DecidableEq C] (B : Matrix ι ι ℝ) (u v : C → ι → ℝ)
    (ch : κ → C) (r : κ → ℝ) (hr : ∀ p, r p ≠ 0) :
    DNonUnstable (star B u v ch r) ↔ ∀ σ : κ → Role, DNonUnstable (bdSystem B u v ch r σ) := by
  rw [← not_iff_not, not_dNonUnstable_iff_dUnstable, dUnstable_iff B u v ch r hr]
  constructor
  · rintro ⟨σ, hσ⟩ hall
    exact (not_dNonUnstable_iff_dUnstable _).mpr hσ (hall σ)
  · intro h
    by_contra hnone
    apply h
    intro σ
    by_contra hσ
    exact hnone ⟨σ, (not_dNonUnstable_iff_dUnstable _).mp hσ⟩

theorem groups_eq_card {κ C : Type*} [Fintype κ] [DecidableEq κ] [Fintype C] [DecidableEq C]
    (ch : κ → C) (σ : κ → Role) (h : ∀ c, ∃ p, ch p = c ∧ σ p = Role.D) :
    groups ch σ = Fintype.card C := by
  unfold groups
  rw [Finset.filter_true_of_mem (fun c _ => h c)]
  rfl

theorem groups_lt_iff (m : ℕ) (σ : Fin (m + 2) → Role) :
    groups (id : Fin (m + 2) → Fin (m + 2)) σ < m + 2 → ∃ c, σ c ≠ Role.D := by
  intro h
  by_contra hall
  push Not at hall
  have := groups_eq_card (id : Fin (m + 2) → Fin (m + 2)) σ (fun c => ⟨c, rfl, hall c⟩)
  rw [Fintype.card_fin] at this
  omega

/-- **Sharpness**, for every number of channels `m + 2`. -/
theorem sharpness (m : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ DUnstable (cycStar m ρ) ∧
    ∀ σ : Fin (m + 2) → Role, groups (id : Fin (m + 2) → Fin (m + 2)) σ < m + 2 →
      DStable (bdSystem (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ) := by
  obtain ⟨ρ, hρ, hbig, hsmall⟩ := cyc_window m
  exact ⟨ρ, hρ, cyc_star_dUnstable m ρ hρ hbig,
    fun σ hσ => cyc_lower_dStable m ρ hρ hsmall σ (groups_lt_iff m σ hσ)⟩

/-- **Example (`k = 2`, `ρ = 9/4`).** The cyclic star `Cyc_2(9/4)` (loop gain `81/16`) is
D-unstable, while every boundary system with fewer than two synchronized groups is D-stable. -/
theorem cyc2_example : DUnstable (cycStar 0 (9 / 4)) ∧
    ∀ σ : Fin 2 → Role, groups (id : Fin 2 → Fin 2) σ < 2 →
      DStable (bdSystem (cycB 0) (cycU 0) (cycV 0) id (fun _ => (9 / 4 : ℝ)) σ) := by
  have h4 : Real.cos (Real.pi / (2 * ((0 : ℕ) + 2))) ^ 2 = 1 / 2 := by
    have : Real.pi / (2 * (((0 : ℕ) : ℝ) + 2)) = Real.pi / 4 := by norm_num
    push_cast at this ⊢
    rw [this, Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h3 : Real.cos (Real.pi / ((2 * (0 + 2) - 1 : ℕ) : ℝ)) = 1 / 2 := by
    have : ((2 * (0 + 2) - 1 : ℕ) : ℝ) = 3 := by norm_num
    rw [this, Real.cos_pi_div_three]
  refine ⟨cyc_star_dUnstable 0 (9 / 4) (by norm_num) ?_, fun σ hσ =>
    cyc_lower_dStable 0 (9 / 4) (by norm_num) ?_ σ (groups_lt_iff 0 σ hσ)⟩
  · push_cast at h4 ⊢
    rw [h4]; norm_num
  · rw [h3]; norm_num

/-- **Sharpness in full** (Theorem 2.7 as printed): for every `k = m + 2` and every `ρ` in the
window, the explicit eigenvalue, D-instability of the star and D-stability of every boundary
system with fewer than `k` groups; and the window is nonempty. -/
theorem sharpness_full (m : ℕ) :
    (∀ ρ : ℝ, 0 < ρ → 1 < ρ * Real.cos (Real.pi / (2 * (m + 2))) ^ 2 →
      ρ ^ (m + 2) * Real.cos (Real.pi / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1 →
      (∃ y, HasEigenpair (rightScale (cycStar m ρ) (fun _ => 1)) (cycEig m ρ) y) ∧
      0 < (cycEig m ρ).re ∧ DUnstable (cycStar m ρ) ∧
      ∀ σ : Fin (m + 2) → Role, groups (id : Fin (m + 2) → Fin (m + 2)) σ < m + 2 →
        DStable (bdSystem (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ)) ∧
    ∃ ρ : ℝ, 0 < ρ ∧ 1 < ρ * Real.cos (Real.pi / (2 * (m + 2))) ^ 2 ∧
      ρ ^ (m + 2) * Real.cos (Real.pi / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1 :=
  ⟨fun ρ hρ hbig hsmall => ⟨cyc_star_eigenpair m ρ hρ, cycEig_re_pos m ρ hρ hbig,
    cyc_star_dUnstable m ρ hρ hbig,
    fun σ hσ => cyc_lower_dStable m ρ hρ hsmall σ (groups_lt_iff m σ hσ)⟩, cyc_window m⟩

/-- **Root declaration**: lifting (any loads); for nonzero loads, spectral localization to
boundary systems with at most one synchronized group per channel, the D-stability criterion and
exact localization of D-semistability; sharpness of the number of synchronized groups for every
number of channels (Theorem 2.7 in full); the marginal-gap example (Proposition 2.6); the
necessity of synchronized groups of two pieces (Proposition 2.8); and the example `k = 2`. -/
theorem localization_and_sharpness :
    (∀ {ι κ C : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype C]
      [DecidableEq C] (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ),
      (∀ σ : κ → Role, DUnstable (bdSystem B u v ch r σ) → DUnstable (star B u v ch r)) ∧
      ((∀ p, r p ≠ 0) →
        (∀ d : ι ⊕ κ → ℝ, (∀ a, 0 < d a) → ∀ z : ℂ, 0 ≤ z.re → ∀ y,
          HasEigenpair (rightScale (star B u v ch r) d) z y →
          ∃ σ : κ → Role, ∃ d' : ι ⊕ C → ℝ, (∀ a, 0 < d' a) ∧ ∃ y',
            HasEigenpair (rightScale (bdSystem B u v ch r σ) d') z y') ∧
        ((∀ σ : κ → Role, DStable (bdSystem B u v ch r σ)) → DStable (star B u v ch r)) ∧
        (DNonUnstable (star B u v ch r) ↔
          ∀ σ : κ → Role, DNonUnstable (bdSystem B u v ch r σ)))) ∧
    (∀ m : ℕ,
      (∀ ρ : ℝ, 0 < ρ → 1 < ρ * Real.cos (Real.pi / (2 * (m + 2))) ^ 2 →
        ρ ^ (m + 2) * Real.cos (Real.pi / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1 →
        (∃ y, HasEigenpair (rightScale (cycStar m ρ) (fun _ => 1)) (cycEig m ρ) y) ∧
        0 < (cycEig m ρ).re ∧ DUnstable (cycStar m ρ) ∧
        ∀ σ : Fin (m + 2) → Role, groups (id : Fin (m + 2) → Fin (m + 2)) σ < m + 2 →
          DStable (bdSystem (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ)) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ 1 < ρ * Real.cos (Real.pi / (2 * (m + 2))) ^ 2 ∧
        ρ ^ (m + 2) * Real.cos (Real.pi / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1) ∧
    ((∀ p, gapR p ≠ 0) ∧ DStable (star gapB gapU gapU gapCh gapR) ∧
      (∃ y, HasEigenpair
        (rightScale (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F)) (fun _ => 1)) I y) ∧
      ¬ DStable (bdSystem gapB gapU gapU gapCh gapR (fun _ => Role.F))) ∧
    ((∀ p, lumpR p ≠ 0) ∧
      (∃ y, HasEigenpair (rightScale (star lumpB lumpU lumpV lumpCh lumpR) (fun _ => 1))
        (lumpMu - 1) y) ∧ 0 < (lumpMu - 1).re ∧
      DUnstable (star lumpB lumpU lumpV lumpCh lumpR) ∧
      ∀ σ : Fin 2 → Role, ¬ (σ 0 = Role.D ∧ σ 1 = Role.D) →
        DStable (bdSystem lumpB lumpU lumpV lumpCh lumpR σ)) ∧
    (DUnstable (cycStar 0 (9 / 4)) ∧
      ∀ σ : Fin 2 → Role, groups (id : Fin 2 → Fin 2) σ < 2 →
        DStable (bdSystem (cycB 0) (cycU 0) (cycV 0) id (fun _ => (9 / 4 : ℝ)) σ)) := by
  refine ⟨fun B u v ch r => ⟨fun σ hσ => dUnstable_of_boundary B u v ch r σ hσ,
      fun hr => ⟨fun d hd z hz y hy => spectral_localization B u v ch r hr d hd z hz y hy,
        dStable_of_boundary B u v ch r hr, dNonUnstable_iff B u v ch r hr⟩⟩,
    sharpness_full, marginal_gap,
    ⟨lumping_needed.1, lump_star_eigenpair, by simp [lumpMu]; norm_num, lumping_needed.2.1,
      lumping_needed.2.2⟩, cyc2_example⟩

end DStabilityLocalization

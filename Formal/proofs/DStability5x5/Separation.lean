import proofs.DStability5x5.Cone

/-!
# Separation protection (Theorem A3)

Let `A₀` be Hurwitz and have no positive contact (`contactDet A₀ d ≠ 0` for all `d > 0`); this
holds for every D-stable matrix and at every *escape* boundary point of the D-stable set.  Then for
every `κ ≥ 1` all matrices near `A₀` are `κ`-stable (`eventually_kStable_of_no_contact`): near such
a point, destabilization needs time-scale separation beyond any fixed bound (`κ*(A) → ∞`).

Equivalently (`contact_of_tendsto_not_kStable`): if `A_k → A₀` with `A₀` Hurwitz and every `A_k`
destabilized within a fixed ratio bound `κ`, then `A₀` has a finite positive contact.

Proof: the homogeneous contact form `G(A; e, ω) = det (iω·1 - A·diag e)` is jointly continuous and
does not vanish on `{A₀} × [1, κ]ⁿ × [0, W]` (at `ω = 0` because `A₀` is nonsingular, for `ω > 0`
because `A₀` has no contact).  The tube lemma gives a neighbourhood of `A₀` on which `G` has no zero
on the compact box, and the row-sum bound excludes `ω > W`.
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- **Theorem A3 (separation protection).** -/
theorem eventually_kStable_of_no_contact {A₀ : Matrix (Fin n) (Fin n) ℝ}
    (hH : HurwitzStable A₀) (hno : ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → contactDet A₀ d ≠ 0)
    {κ : ℝ} (hκ : 1 ≤ κ) : ∀ᶠ A in 𝓝 A₀, KStable κ A := by
  set R₀ : ℝ := ∑ i, ∑ j, |A₀ i j| with hR₀
  set W : ℝ := κ * (R₀ + (n : ℝ) * n) + 1 with hW
  let X : Set ((Fin n → ℝ) × ℝ) :=
    (Set.pi Set.univ (fun _ => Set.Icc 1 κ)) ×ˢ Set.Icc 0 W
  have hXc : IsCompact X := (isCompact_univ_pi (fun _ => isCompact_Icc)).prod isCompact_Icc
  -- the form does not vanish at A₀ on X
  have hA₀X : ∀ x ∈ X, homContact A₀ x ≠ 0 := by
    intro x hx hG
    have hbox : ∀ i, 1 ≤ x.1 i := fun i => (hx.1 i (Set.mem_univ i)).1
    rcases eq_or_lt_of_le hx.2.1 with h0 | hpos
    · obtain ⟨v, hv⟩ := (homContact_eq_zero_iff A₀ x).mp hG
      rw [← h0] at hv
      simp only [Complex.ofReal_zero, zero_mul] at hv
      exact no_zero_eigen_of_hurwitz A₀ hH x.1 (fun i => lt_of_lt_of_le one_pos (hbox i)) v hv
    · have hG' : homContact A₀ (x.1, x.2) = 0 := hG
      rw [homContact_eq_zero_iff_contact A₀ x.1 hpos] at hG'
      exact hno _ (fun i => mul_pos (inv_pos.mpr hpos) (lt_of_lt_of_le one_pos (hbox i))) hG'
  -- tube lemma
  have hP : ∀ x ∈ X, ∀ᶠ z : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ) in 𝓝 (A₀, x),
      homContact z.1 z.2 ≠ 0 := by
    intro x hx
    have hcont : ContinuousAt
        (fun z : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × ℝ) => homContact z.1 z.2) (A₀, x) :=
      continuous_homContact_joint.continuousAt
    exact hcont.eventually_ne (hA₀X x hx)
  have htube : ∀ᶠ A in 𝓝 A₀, ∀ x ∈ X, homContact A x ≠ 0 :=
    hXc.eventually_forall_of_forall_eventually (P := fun A x => homContact A x ≠ 0) hP
  -- entries stay within 1 of A₀
  have hnear : ∀ᶠ A in 𝓝 A₀, ∀ i j, |A i j - A₀ i j| < 1 := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) :=
      (continuous_apply j).comp (continuous_apply i)
    filter_upwards [hc.continuousAt.eventually (Metric.ball_mem_nhds (A₀ i j) one_pos)] with A hA
    rw [Real.dist_eq] at hA
    exact hA
  filter_upwards [htube, hnear, isOpen_hurwitzStable.mem_nhds hH] with A hA hAn hAH
  rw [kStable_iff_no_cone_contact hκ]
  refine ⟨hAH, ?_⟩
  rintro ⟨d, hd, hc⟩
  obtain ⟨x, hxbox, hxpos, hxG⟩ := exists_box_of_cone_contact A hd hc
  have hfreq := abs_freq_le_of_homContact A
    (fun i => ⟨le_trans zero_le_one (hxbox i).1, (hxbox i).2⟩) hxG
  have hsum : ∑ i, ∑ j, |A i j| ≤ R₀ + (n : ℝ) * n := by
    have h1 : ∑ i, ∑ j, |A i j| ≤ ∑ i : Fin n, ∑ j : Fin n, (|A₀ i j| + 1) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := hAn i j
      have h2 : |A i j| ≤ |A₀ i j| + |A i j - A₀ i j| := by
        have := abs_add_le (A₀ i j) (A i j - A₀ i j)
        simpa using this
      linarith
    have h2 : ∑ i : Fin n, ∑ j : Fin n, (|A₀ i j| + 1) = R₀ + (n : ℝ) * n := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, hR₀]
    linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hxW : x.2 ≤ W := by
    have h1 : x.2 ≤ κ * ∑ i, ∑ j, |A i j| := le_trans (le_abs_self _) hfreq
    have h2 : κ * ∑ i, ∑ j, |A i j| ≤ κ * (R₀ + (n : ℝ) * n) :=
      mul_le_mul_of_nonneg_left hsum hκ0
    linarith
  exact hA x ⟨fun i _ => hxbox i, hxpos.le, hxW⟩ hxG

/-- Sequential form: bounded destabilizing ratios along `A_k → A₀` force a finite contact of `A₀`. -/
theorem contact_of_tendsto_not_kStable {A₀ : Matrix (Fin n) (Fin n) ℝ} (hH : HurwitzStable A₀)
    {u : ℕ → Matrix (Fin n) (Fin n) ℝ} (hu : Tendsto u atTop (𝓝 A₀)) {κ : ℝ} (hκ : 1 ≤ κ)
    (hK : ∀ k, ¬ KStable κ (u k)) : ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ contactDet A₀ d = 0 := by
  by_contra h
  push Not at h
  obtain ⟨k, hk⟩ := (hu.eventually (eventually_kStable_of_no_contact hH h hκ)).exists
  exact hK k hk

/-- D-stable matrices have no positive contact, so bounded time-scale stability is robust around
them (although the D-stable set itself is not open). -/
theorem eventually_kStable_of_dStable {A₀ : Matrix (Fin n) (Fin n) ℝ} (hA₀ : DStable A₀)
    {κ : ℝ} (hκ : 1 ≤ κ) : ∀ᶠ A in 𝓝 A₀, KStable κ A := by
  refine eventually_kStable_of_no_contact (by simpa using hA₀ (fun _ => 1) (fun _ => one_pos))
    ?_ hκ
  intro d hd hc
  obtain ⟨v, hv⟩ := (contact_iff_eigenpair A₀ d).mp hc
  have h := hA₀ d hd Complex.I v hv
  simp at h

end DStability5x5

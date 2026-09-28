import proofs.DStabilityLocalization.ChannelInduction

/-!
# Real eigenvalues in the closed right half-plane

* `zero_eigen_static`: a zero eigenvalue of a positive scaling of the star is a zero
  eigenvalue of the all-static boundary system, with the same core scaling.
* `localization_real`: a real positive eigenvalue `λ` of a positive scaling of the star is the
  same eigenvalue of a positive scaling of the boundary system in which, in every channel, the
  pieces whose load has the sign of the channel value form the synchronized group and the other
  pieces are slow (no fast pieces; same core scaling).  At a real `λ > 0` every piece contributes `r_p a_p` with `a_p ∈ (0,1)`, so the
  channel value lies strictly between the sums of its negative and of its positive loads.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable {ι κ C : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype C] [DecidableEq C]

theorem lagValue_zero (ch : κ → C) (r t : κ → ℝ) (c : C) :
    lagValue ch r t 0 c = ∑ p, if ch p = c then (r p : ℂ) else 0 := by
  unfold lagValue
  simp

/-- A zero eigenvalue of the star is a zero eigenvalue of the all-static boundary system. -/
theorem zero_eigen_static (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (d : ι ⊕ κ → ℝ) (hd : ∀ a, 0 < d a) (y : ι ⊕ κ → ℂ)
    (hy : HasEigenpair (rightScale (star B u v ch r) d) 0 y) :
    ∃ d' : ι ⊕ C → ℝ, (∀ a, 0 < d' a) ∧ (∀ i, d' (.inl i) = d (.inl i)) ∧ ∃ y',
      HasEigenpair (rightScale (bdSystem B u v ch r (fun _ => Role.F)) d') 0 y' := by
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair B u v ch r d hd 0 y hy (by simp)
  set q : ι → ℝ := fun i => (d (.inl i))⁻¹
  have hq : ∀ i, 0 < q i := fun i => inv_pos.mpr (hd _)
  have hpen : pencil B u v q (lagValue ch r (fun p => (d (.inr p))⁻¹) 0) 0 =
      pencil (bdCore B u v ch r (fun _ => Role.F)) u v q
        (lagValue id (bdLoad ch r (fun _ => Role.F)) (fun _ => 1) 0) 0 := by
    ext i j
    simp only [pencil, bdCore, lagValue_zero, bdLoad]
    have hreg := sum_channel_regroup ch (fun p => (r p : ℂ))
      (fun c => (u c i : ℂ) * (v c j : ℂ))
    simp only [mul_assoc] at hreg ⊢
    simp [hreg]
    ring
  rw [hpen] at hker
  obtain ⟨y', hy'⟩ := eigenpair_of_pencil_kernel (bdCore B u v ch r (fun _ => Role.F)) u v id
    (bdLoad ch r (fun _ => Role.F)) q (fun _ => 1) hq (fun _ => one_pos) 0 (by simp) x hx hker
  refine ⟨_, ?_, fun i => by simp [q], y', hy'⟩
  intro a
  rcases a with i | c
  · exact inv_pos.mpr (hq i)
  · simp

/-- Sum of the positive loads of channel `c`. -/
def posLoad (ch : κ → C) (r : κ → ℝ) (c : C) : ℝ :=
  ∑ p, if ch p = c ∧ 0 < r p then r p else 0

/-- Sum of the negative loads of channel `c`. -/
def negLoad (ch : κ → C) (r : κ → ℝ) (c : C) : ℝ :=
  ∑ p, if ch p = c ∧ r p < 0 then r p else 0

/-- Roles for a real eigenvalue with real channel values `L`: the pieces whose load has the sign
of their channel value are synchronized, all others are slow. -/
def realRole (ch : κ → C) (r : κ → ℝ) (L : C → ℝ) (p : κ) : Role :=
  if (0 < L (ch p) ∧ 0 < r p) ∨ (L (ch p) < 0 ∧ r p < 0) then Role.D else Role.S

theorem bdCore_of_noF (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (σ : κ → Role) (hσ : ∀ p, σ p ≠ Role.F) : bdCore B u v ch r σ = B := by
  ext i j
  simp [bdCore, hσ]

theorem bdLoad_realRole (ch : κ → C) (r : κ → ℝ) (L : C → ℝ) (c : C) :
    bdLoad ch r (realRole ch r L) c =
      if 0 < L c then posLoad ch r c else if L c < 0 then negLoad ch r c else 0 := by
  unfold bdLoad
  by_cases hpos : 0 < L c
  · rw [if_pos hpos]
    unfold posLoad
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hc : ch p = c
    · have hn : ¬ L c < 0 := not_lt.mpr hpos.le
      by_cases hr : 0 < r p
      · simp [realRole, hc, hpos, hr]
      · simp [realRole, hc, hpos, hr, hn]
    · simp [hc]
  · rw [if_neg hpos]
    by_cases hneg : L c < 0
    · rw [if_pos hneg]
      unfold negLoad
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hc : ch p = c
      · by_cases hr : r p < 0
        · simp [realRole, hc, hneg, hr]
        · simp [realRole, hc, hpos, hr]
      · simp [hc]
    · rw [if_neg hneg]
      refine Finset.sum_eq_zero (fun p _ => ?_)
      by_cases hc : ch p = c
      · simp [realRole, hc, hpos, hneg]
      · simp [hc]

/-- A channel value with factors in `(0,1)` lies strictly below the positive load sum when it is
positive. -/
theorem lt_posLoad (ch : κ → C) (r a : κ → ℝ) (ha0 : ∀ p, 0 < a p) (ha1 : ∀ p, a p < 1)
    (c : C) (hL : 0 < ∑ p, if ch p = c then r p * a p else 0) :
    (∑ p, if ch p = c then r p * a p else 0) < posLoad ch r c := by
  unfold posLoad
  by_cases hex : ∃ p, ch p = c ∧ 0 < r p
  · obtain ⟨p₀, hp₀c, hp₀r⟩ := hex
    apply Finset.sum_lt_sum
    · intro p _
      by_cases hc : ch p = c
      · by_cases hr : 0 < r p
        · simp only [hc, hr, and_self, if_true]
          nlinarith [ha1 p]
        · simp only [hc, hr, and_false, if_false, if_true]
          have : r p ≤ 0 := not_lt.mp hr
          nlinarith [ha0 p]
      · simp [hc]
    · refine ⟨p₀, Finset.mem_univ _, ?_⟩
      simp only [hp₀c, hp₀r, and_self, if_true]
      nlinarith [ha1 p₀]
  · push Not at hex
    exfalso
    have : (∑ p, if ch p = c then r p * a p else 0) ≤ 0 := by
      apply Finset.sum_nonpos
      intro p _
      by_cases hc : ch p = c
      · simp only [hc, if_true]
        nlinarith [hex p hc, ha0 p]
      · simp [hc]
    linarith

theorem negLoad_lt (ch : κ → C) (r a : κ → ℝ) (ha0 : ∀ p, 0 < a p) (ha1 : ∀ p, a p < 1)
    (c : C) (hL : (∑ p, if ch p = c then r p * a p else 0) < 0) :
    negLoad ch r c < ∑ p, if ch p = c then r p * a p else 0 := by
  have h := lt_posLoad ch (fun p => -r p) a ha0 ha1 c (by
    have : (∑ p, if ch p = c then -r p * a p else 0) =
        -(∑ p, if ch p = c then r p * a p else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      split_ifs <;> ring
    rw [this]; linarith)
  have e1 : (∑ p, if ch p = c then -r p * a p else 0) =
      -(∑ p, if ch p = c then r p * a p else 0) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> ring
  have e2 : posLoad ch (fun p => -r p) c = -negLoad ch r c := by
    unfold posLoad negLoad
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hc : ch p = c
    · by_cases hr : r p < 0
      · simp [hc, hr]
      · have : ¬ 0 < -r p := by linarith [not_lt.mp hr]
        simp [hc, hr, this]
    · simp [hc]
  rw [e1, e2] at h
  linarith

/-- **Localization of real positive eigenvalues.** If a positive scaling of the star has a real
eigenvalue `z > 0`, then some boundary system (without fast pieces) has the same eigenvalue at a
positive scaling. -/
theorem localization_real (B : Matrix ι ι ℝ) (u v : C → ι → ℝ) (ch : κ → C) (r : κ → ℝ)
    (d : ι ⊕ κ → ℝ) (hd : ∀ a, 0 < d a) {z : ℂ} (hre : 0 < z.re) (him : z.im = 0)
    (y : ι ⊕ κ → ℂ) (hy : HasEigenpair (rightScale (star B u v ch r) d) z y) :
    ∃ σ : κ → Role, (∀ p, σ p ≠ Role.F) ∧ ∃ d' : ι ⊕ C → ℝ, (∀ a, 0 < d' a) ∧
      (∀ i, d' (.inl i) = d (.inl i)) ∧ ∃ y',
      HasEigenpair (rightScale (bdSystem B u v ch r σ) d') z y' := by
  set x0 := z.re with hx0
  have hzreal : z = (x0 : ℂ) := Complex.ext (by simp [hx0]) (by simp [him])
  set t : κ → ℝ := fun p => (d (.inr p))⁻¹
  have ht : ∀ p, 0 < t p := fun p => inv_pos.mpr (hd _)
  have hz1 : ∀ p, 1 + z * ((d (.inr p))⁻¹ : ℝ) ≠ 0 :=
    fun p => one_add_mul_ne hre.le (ht p).le
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair B u v ch r d hd _ y hy hz1
  -- real factors and channel values
  set a : κ → ℝ := fun p => 1 / (1 + x0 * t p)
  have hden : ∀ p, 0 < 1 + x0 * t p := fun p => by nlinarith [mul_pos hre (ht p)]
  have ha0 : ∀ p, 0 < a p := fun p => one_div_pos.mpr (hden p)
  have ha1 : ∀ p, a p < 1 := fun p => by
    show 1 / (1 + x0 * t p) < 1
    rw [div_lt_one (hden p)]; nlinarith [mul_pos hre (ht p)]
  set L : C → ℝ := fun c => ∑ p, if ch p = c then r p * a p else 0
  have hlag : ∀ c, lagValue ch r t z c = (L c : ℂ) := by
    intro c
    unfold lagValue
    simp only [L]
    push_cast
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · rw [hzreal]
      have : (1 + (x0 : ℂ) * (t p : ℂ)) ≠ 0 := by exact_mod_cast (hden p).ne'
      simp only [a]
      push_cast
      field_simp
    · rfl
  set σ := realRole ch r L
  set R := bdLoad ch r σ
  set tc : C → ℝ := fun c => if L c = 0 then 1 else (R c / L c - 1) / x0
  have hRL : ∀ c, L c ≠ 0 → 1 < R c / L c := by
    intro c hc
    have hR := bdLoad_realRole ch r L c
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have hnp : ¬ 0 < L c := not_lt.mpr hneg.le
      simp only [R, σ] at hR ⊢
      rw [hR, if_neg hnp, if_pos hneg]
      have := negLoad_lt ch r a ha0 ha1 c hneg
      rw [lt_div_iff_of_neg hneg]
      linarith
    · simp only [R, σ] at hR ⊢
      rw [hR, if_pos hpos]
      have := lt_posLoad ch r a ha0 ha1 c hpos
      rw [lt_div_iff₀ hpos]
      linarith
  have htc : ∀ c, 0 < tc c := by
    intro c
    simp only [tc]
    split_ifs with hc
    · exact one_pos
    · exact div_pos (by linarith [hRL c hc]) hre
  have hR0 : ∀ c, L c = 0 → R c = 0 := by
    intro c hc
    have hR := bdLoad_realRole ch r L c
    simp only [R, σ] at hR ⊢
    rw [hR, if_neg (by rw [hc]; exact lt_irrefl 0), if_neg (by rw [hc]; exact lt_irrefl 0)]
  have hlump : ∀ c, lagValue id R tc z c = (L c : ℂ) := by
    intro c
    have e : lagValue id R tc z c = (R c : ℂ) / (1 + z * (tc c : ℂ)) := by
      show (∑ p : C, if p = c then (R p : ℂ) / (1 + z * (tc p : ℂ)) else 0) = _
      rw [Fintype.sum_eq_single c (fun x hx => if_neg hx), if_pos rfl]
    rw [e]
    by_cases hc : L c = 0
    · rw [hR0 c hc, hc]; simp
    · have hdc : (1 : ℝ) + x0 * tc c = R c / L c := by
        simp only [tc, if_neg hc]
        field_simp
        ring
      have hRne : R c ≠ 0 := by
        intro h0; have := hRL c hc; rw [h0, zero_div] at this; linarith
      rw [hzreal]
      have hcast : (1 : ℂ) + (x0 : ℂ) * (tc c : ℂ) = ((R c / L c : ℝ) : ℂ) := by
        rw [← hdc]; push_cast; ring
      rw [hcast]
      have hRc : (R c : ℂ) ≠ 0 := by exact_mod_cast hRne
      have hLc : (L c : ℂ) ≠ 0 := by exact_mod_cast hc
      push_cast
      field_simp
  have hnoF : ∀ p, σ p ≠ Role.F := by
    intro p
    simp only [σ, realRole]
    split_ifs <;> simp
  have hpen : pencil B u v (fun i => (d (.inl i))⁻¹) (lagValue ch r t z) z =
      pencil (bdCore B u v ch r σ) u v (fun i => (d (.inl i))⁻¹) (lagValue id R tc z) z := by
    rw [bdCore_of_noF B u v ch r σ hnoF]
    ext i j
    simp only [pencil, hlag, hlump]
  rw [hpen] at hker
  have hzc : ∀ c, 1 + z * (tc c : ℂ) ≠ 0 := fun c => one_add_mul_ne hre.le (htc c).le
  obtain ⟨y', hy'⟩ := eigenpair_of_pencil_kernel (bdCore B u v ch r σ) u v id R
    (fun i => (d (.inl i))⁻¹) tc (fun i => inv_pos.mpr (hd _)) htc z hzc x hx hker
  refine ⟨σ, hnoF, _, ?_, fun i => by simp, y', hy'⟩
  intro b
  rcases b with i | c
  · simp only [Sum.elim_inl]; exact inv_pos.mpr (inv_pos.mpr (hd _))
  · simp only [Sum.elim_inr]; exact inv_pos.mpr (htc c)

end DStabilityLocalization

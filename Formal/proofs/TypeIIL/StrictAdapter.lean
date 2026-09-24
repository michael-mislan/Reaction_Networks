import Mathlib
import proofs.TypeIIL.StrictModel

namespace TypeIIL

def forkCurrent (p q : Reaction l → ℝ) (j : Fin l) : ℝ :=
  p (.inl j) - q (.inl j)

def simpleCurrent (p q : Reaction l → ℝ) (j : Fin l) : ℝ :=
  p (.inr j) - q (.inr j)

def forkRatioCurrent (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (j : Fin l) : ℝ :=
  rho (.inl j) * p (.inl j) -
    (rho (.inr j) * rho (.inr (d.next j)) ^ d.m j) * q (.inl j)

def simpleRatioCurrent (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (j : Fin l) : ℝ :=
  rho (.inr j) * p (.inr j) - rho (.inl j) * q (.inr j)

def backRatio (rho : Species l → ℝ) (j : Fin l) : ℝ := rho (.inr j)
def forkRatio (rho : Species l → ℝ) (j : Fin l) : ℝ := rho (.inl j)
def ratioDelta (rho : Species l → ℝ) (j : Fin l) : ℝ :=
  backRatio rho j - forkRatio rho j
def residualFlow (p q : Reaction l → ℝ) (j : Fin l) : ℝ :=
  p (.inr j) - forkCurrent p q j

theorem strictStoich_fork_sum (d : StrictData l)
    (z : Reaction l → ℝ) (j : Fin l) :
    ∑ r, strictStoich d (.inl j) r * z r = -z (.inl j) + z (.inr j) := by
  simp [strictStoich, Fintype.sum_sum_type]

theorem strictStoich_back_sum (d : StrictData l)
    (z : Reaction l → ℝ) (i : Fin l) :
    ∑ r, strictStoich d (.inr i) r * z r =
      z (.inl i) + d.m (d.next.symm i) * z (.inl (d.next.symm i)) - z (.inr i) := by
  have hincoming :
      (∑ j, (if i = d.next j then (d.m j : ℝ) else 0) * z (.inl j)) =
      d.m (d.next.symm i) * z (.inl (d.next.symm i)) := by
    classical
    rw [show d.m (d.next.symm i) * z (.inl (d.next.symm i)) =
      (if i = d.next (d.next.symm i) then (d.m (d.next.symm i) : ℝ) else 0) *
        z (.inl (d.next.symm i)) by simp]
    apply Fintype.sum_eq_single (d.next.symm i)
    intro b hb
    rw [if_neg]
    · simp
    · intro hib
      apply hb
      apply d.next.injective
      simpa using hib.symm
  simp only [strictStoich, Fintype.sum_sum_type]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [hincoming]
  simp
  ring

theorem strict_base_fork_row
    (d : StrictData l) (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e) (j : Fin l) :
    -forkCurrent p q j + simpleCurrent p q j = e (.inl j) := by
  simpa [TypeII3.BaseFluxBalance, strictStoich, forkCurrent, simpleCurrent,
    Fintype.sum_sum_type] using hB (.inl j)

theorem strict_ratio_fork_row
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    -forkRatioCurrent d rho p q j + simpleRatioCurrent rho p q j =
      rho (.inl j) * e (.inl j) := by
  simpa [TypeII3.RatioFluxBalance, strictStoich, strictAlpha, strictBeta,
    forkRatioCurrent, simpleRatioCurrent, Fintype.sum_sum_type] using hR (.inl j)

theorem strict_local_ratio_identity
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    (rho (.inr j) - rho (.inl j)) * p (.inr j) +
      (rho (.inr j) * rho (.inr (d.next j)) ^ d.m j - rho (.inl j)) *
        q (.inl j) = 0 := by
  have hb := strict_base_fork_row d p q e hB j
  have hr := strict_ratio_fork_row d rho p q e hR j
  simp only [forkCurrent, simpleCurrent, forkRatioCurrent,
    simpleRatioCurrent] at hb hr
  linear_combination hr - rho (.inl j) * hb

theorem strict_ratio_delta_neg_iff
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hrho : ∀ i, 0 < rho i) (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    ratioDelta rho j < 0 ↔ 1 < backRatio rho (d.next j) := by
  have hl := strict_local_ratio_identity d rho p q e hB hR j
  have heq : ratioDelta rho j * (p (.inr j) + q (.inl j)) +
      backRatio rho j * (backRatio rho (d.next j) ^ d.m j - 1) *
        q (.inl j) = 0 := by
    simp only [ratioDelta, backRatio, forkRatio] at hl ⊢
    linear_combination hl
  have hP : 0 < p (.inr j) + q (.inl j) := add_pos (hp _) (hq _)
  have hy : 0 < backRatio rho j := hrho _
  have hQ : 0 < q (.inl j) := hq _
  have hm0 : d.m j ≠ 0 := Nat.ne_of_gt (d.m_pos j)
  constructor
  · intro hdlt
    have hterm1 : ratioDelta rho j * (p (.inr j) + q (.inl j)) < 0 :=
      mul_neg_of_neg_of_pos hdlt hP
    have hterm2 : 0 < backRatio rho j *
        (backRatio rho (d.next j) ^ d.m j - 1) * q (.inl j) := by linarith
    have hmid : 0 < backRatio rho (d.next j) ^ d.m j - 1 := by
      rcases (mul_pos_iff.mp hterm2) with h | h
      · rcases (mul_pos_iff.mp h.1) with h' | h'
        · exact h'.2
        · exact False.elim ((not_lt_of_ge (le_of_lt hy)) h'.1)
      · exact False.elim ((not_lt_of_ge (le_of_lt hQ)) h.2)
    exact (one_lt_pow_iff_of_nonneg (le_of_lt (hrho _)) hm0).mp
      (sub_pos.mp hmid)
  · intro hz
    have hpow : 1 < backRatio rho (d.next j) ^ d.m j :=
      (one_lt_pow_iff_of_nonneg (le_of_lt (hrho _)) hm0).2 hz
    have hterm2 : 0 < backRatio rho j *
        (backRatio rho (d.next j) ^ d.m j - 1) * q (.inl j) := by positivity
    have hterm1 : ratioDelta rho j * (p (.inr j) + q (.inl j)) < 0 := by linarith
    rcases (mul_neg_iff.mp hterm1) with h | h
    · exact False.elim ((not_lt_of_ge (le_of_lt hP)) h.2)
    · exact h.1

theorem strict_ratio_delta_pos_iff
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hrho : ∀ i, 0 < rho i) (hp : ∀ r, 0 < p r) (hq : ∀ r, 0 < q r)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    0 < ratioDelta rho j ↔ backRatio rho (d.next j) < 1 := by
  have hl := strict_local_ratio_identity d rho p q e hB hR j
  have heq : ratioDelta rho j * (p (.inr j) + q (.inl j)) +
      backRatio rho j * (backRatio rho (d.next j) ^ d.m j - 1) *
        q (.inl j) = 0 := by
    simp only [ratioDelta, backRatio, forkRatio] at hl ⊢
    linear_combination hl
  have hP : 0 < p (.inr j) + q (.inl j) := add_pos (hp _) (hq _)
  have hy : 0 < backRatio rho j := hrho _
  have hQ : 0 < q (.inl j) := hq _
  have hz0 : 0 ≤ backRatio rho (d.next j) := le_of_lt (hrho _)
  have hm0 : d.m j ≠ 0 := Nat.ne_of_gt (d.m_pos j)
  constructor
  · intro hdgt
    have hterm1 : 0 < ratioDelta rho j * (p (.inr j) + q (.inl j)) :=
      mul_pos hdgt hP
    have hterm2 : backRatio rho j *
        (backRatio rho (d.next j) ^ d.m j - 1) * q (.inl j) < 0 := by linarith
    have hmid : backRatio rho (d.next j) ^ d.m j - 1 < 0 := by
      rcases (mul_neg_iff.mp hterm2) with h | h
      · exact False.elim ((not_lt_of_ge (le_of_lt hQ)) h.2)
      · rcases (mul_neg_iff.mp h.1) with h' | h'
        · exact h'.2
        · exact False.elim ((not_lt_of_ge (le_of_lt hy)) h'.1)
    exact (pow_lt_one_iff_of_nonneg hz0 hm0).mp (by linarith)
  · intro hz
    have hpow : backRatio rho (d.next j) ^ d.m j < 1 :=
      (pow_lt_one_iff_of_nonneg hz0 hm0).2 hz
    have hterm2 : backRatio rho j *
        (backRatio rho (d.next j) ^ d.m j - 1) * q (.inl j) < 0 := by
      have : backRatio rho (d.next j) ^ d.m j - 1 < 0 := by linarith
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hy this) hQ
    have hterm1 : 0 < ratioDelta rho j * (p (.inr j) + q (.inl j)) := by linarith
    rcases (mul_pos_iff.mp hterm1) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (le_of_lt hP)) h.2)

theorem strict_fork_ratio_rewrite
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    forkRatioCurrent d rho p q j =
      backRatio rho j * forkCurrent p q j +
        ratioDelta rho j * residualFlow p q j := by
  have hl := strict_local_ratio_identity d rho p q e hB hR j
  simp only [forkRatioCurrent, backRatio, forkRatio, ratioDelta,
    residualFlow, forkCurrent] at hl ⊢
  linear_combination -hl

theorem strict_base_back_row
    (d : StrictData l) (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e) (i : Fin l) :
    forkCurrent p q i +
      d.m (d.next.symm i) * forkCurrent p q (d.next.symm i) -
      simpleCurrent p q i = e (.inr i) := by
  have hincoming :
      (∑ j, (if i = d.next j then (d.m j : ℝ) else 0) *
        forkCurrent p q j) =
      d.m (d.next.symm i) * forkCurrent p q (d.next.symm i) := by
    classical
    rw [show d.m (d.next.symm i) * forkCurrent p q (d.next.symm i) =
      (if i = d.next (d.next.symm i) then (d.m (d.next.symm i) : ℝ) else 0) *
        forkCurrent p q (d.next.symm i) by simp]
    apply Fintype.sum_eq_single (d.next.symm i)
    intro b hb
    rw [if_neg]
    · simp
    · intro hib
      apply hb
      apply d.next.injective
      simpa using hib.symm
  have hown : (∑ j, (if i = j then (1 : ℝ) else 0) * forkCurrent p q j) =
      forkCurrent p q i := by
    classical
    rw [show forkCurrent p q i =
      (if i = i then (1 : ℝ) else 0) * forkCurrent p q i by simp]
    apply Fintype.sum_eq_single i
    intro b hb
    rw [if_neg (Ne.symm hb)]
    simp
  have hsimple : (∑ j, (if i = j then (-1 : ℝ) else 0) * simpleCurrent p q j) =
      -simpleCurrent p q i := by
    classical
    rw [show -simpleCurrent p q i =
      (if i = i then (-1 : ℝ) else 0) * simpleCurrent p q i by simp]
    apply Fintype.sum_eq_single i
    intro b hb
    rw [if_neg (Ne.symm hb)]
    simp
  have h := hB (.inr i)
  simp only [strictStoich, Fintype.sum_sum_type] at h
  simp_rw [add_mul, Finset.sum_add_distrib] at h
  simp only [Nat.cast_ite, Nat.cast_zero] at h
  change ((∑ j, (if i = j then (1 : ℝ) else 0) * forkCurrent p q j) +
      (∑ j, (if i = d.next j then (d.m j : ℝ) else 0) * forkCurrent p q j)) +
      (∑ j, (if i = j then (-1 : ℝ) else 0) * simpleCurrent p q j) =
      e (.inr i) at h
  rw [hown, hincoming, hsimple] at h
  ring_nf at h
  exact h

theorem strict_ratio_back_row
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (i : Fin l) :
    forkRatioCurrent d rho p q i +
      d.m (d.next.symm i) * forkRatioCurrent d rho p q (d.next.symm i) -
      simpleRatioCurrent rho p q i = rho (.inr i) * e (.inr i) := by
  let F : Fin l → ℝ := forkRatioCurrent d rho p q
  let S : Fin l → ℝ := simpleRatioCurrent rho p q
  have hincoming :
      (∑ j, (if i = d.next j then (d.m j : ℝ) else 0) * F j) =
      d.m (d.next.symm i) * F (d.next.symm i) := by
    classical
    rw [show d.m (d.next.symm i) * F (d.next.symm i) =
      (if i = d.next (d.next.symm i) then (d.m (d.next.symm i) : ℝ) else 0) *
        F (d.next.symm i) by simp]
    apply Fintype.sum_eq_single (d.next.symm i)
    intro b hb
    rw [if_neg]
    · simp
    · intro hib
      apply hb
      apply d.next.injective
      simpa using hib.symm
  have hown : (∑ j, (if i = j then (1 : ℝ) else 0) * F j) = F i := by
    classical
    rw [show F i = (if i = i then (1 : ℝ) else 0) * F i by simp]
    apply Fintype.sum_eq_single i
    intro b hb
    rw [if_neg (Ne.symm hb)]
    simp
  have hsimple : (∑ j, (if i = j then (-1 : ℝ) else 0) * S j) = -S i := by
    classical
    rw [show -S i = (if i = i then (-1 : ℝ) else 0) * S i by simp]
    apply Fintype.sum_eq_single i
    intro b hb
    rw [if_neg (Ne.symm hb)]
    simp
  have h := hR (.inr i)
  simp only [strictStoich, Fintype.sum_sum_type] at h
  simp_rw [add_mul, Finset.sum_add_distrib] at h
  simp only [Nat.cast_ite, Nat.cast_zero] at h
  change ((∑ j, (if i = j then (1 : ℝ) else 0) * F j) +
      (∑ j, (if i = d.next j then (d.m j : ℝ) else 0) * F j)) +
      (∑ j, (if i = j then (-1 : ℝ) else 0) * S j) =
      rho (.inr i) * e (.inr i) at h
  rw [hown, hincoming, hsimple] at h
  dsimp [F, S] at h
  ring_nf at h ⊢
  exact h

theorem strict_fork_current_pos
    (d : StrictData l) (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (he : ∀ i, 0 < e i)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e) (j : Fin l) :
    0 < forkCurrent p q j := by
  have hf := strict_base_fork_row d p q e hB (d.next j)
  have hs := strict_base_back_row d p q e hB (d.next j)
  rw [d.next.symm_apply_apply] at hs
  have hmpos : 0 < (d.m j : ℝ) := by exact_mod_cast d.m_pos j
  have hprod : 0 < (d.m j : ℝ) * forkCurrent p q j := by
    linarith [he (.inl (d.next j)), he (.inr (d.next j))]
  rcases (mul_pos_iff.mp hprod) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge (le_of_lt hmpos)) h.1)

theorem strict_residual_gt_degradation
    (d : StrictData l) (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hq : ∀ r, 0 < q r)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e) (j : Fin l) :
    e (.inl j) < residualFlow p q j := by
  have hf := strict_base_fork_row d p q e hB j
  simp only [forkCurrent, simpleCurrent, residualFlow] at hf ⊢
  linarith [hq (.inr j)]

theorem strict_cyclic_recurrence
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) (j : Fin l) :
    d.m j *
        (forkCurrent p q j * (backRatio rho j - backRatio rho (d.next j)) +
          residualFlow p q j * ratioDelta rho j) +
      e (.inl (d.next j)) * ratioDelta rho (d.next j) = 0 := by
  have hbf := strict_base_fork_row d p q e hB (d.next j)
  have hbs := strict_base_back_row d p q e hB (d.next j)
  have hrf := strict_ratio_fork_row d rho p q e hR (d.next j)
  have hrs := strict_ratio_back_row d rho p q e hR (d.next j)
  have hrewrite := strict_fork_ratio_rewrite d rho p q e hB hR j
  rw [d.next.symm_apply_apply] at hbs hrs
  simp only [backRatio, forkRatio, ratioDelta] at hbf hbs hrf hrs hrewrite ⊢
  linear_combination
    hrs + hrf - rho (.inr (d.next j)) * (hbs + hbf) - d.m j * hrewrite

/-- Source-faithful strict-gap Type II_l positive-kernel theorem.  No
separator-completeness assumption remains: the cyclic sign/product argument
constructs the contradiction directly. -/
theorem strict_positive_kernel_ratios_all_one_unconditional
    [NeZero l]
    (d : StrictData l) (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) (he : ∀ i, 0 < e i)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) :
    AllRatiosOne rho := by
  have hback : ∀ j, backRatio rho j = 1 := by
    by_contra h
    push Not at h
    have hfalse := cyclic_sign_product_contradiction
      d.next d.next_singleCycle
      (fun j => (d.m j : ℝ))
      (forkCurrent p q) (residualFlow p q)
      (fun j => e (.inl j)) (backRatio rho) (ratioDelta rho)
      (fun j => by
        have hj : 1 ≤ d.m j := d.m_pos j
        change (1 : ℝ) ≤ (d.m j : ℝ)
        exact_mod_cast hj)
      (strict_fork_current_pos d p q e he hB)
      (fun j => lt_trans (he (.inl j))
        (strict_residual_gt_degradation d p q e hq hB j))
      (fun j => he (.inl j))
      (strict_residual_gt_degradation d p q e hq hB)
      (strict_ratio_delta_neg_iff d rho p q e hrho hp hq hB hR)
      (strict_ratio_delta_pos_iff d rho p q e hrho hp hq hB hR)
      (strict_cyclic_recurrence d rho p q e hB hR)
      h
    exact hfalse
  intro i
  cases i with
  | inr j => exact hback j
  | inl j =>
      have hn := strict_ratio_delta_neg_iff d rho p q e hrho hp hq hB hR j
      have hp' := strict_ratio_delta_pos_iff d rho p q e hrho hp hq hB hR j
      have hnext : backRatio rho (d.next j) = 1 := hback (d.next j)
      have hdelta : ratioDelta rho j = 0 := by
        rcases lt_trichotomy (ratioDelta rho j) 0 with hlt | heq | hgt
        · have : 1 < backRatio rho (d.next j) := hn.mp hlt
          linarith
        · exact heq
        · have : backRatio rho (d.next j) < 1 := hp'.mp hgt
          linarith
      have hj := hback j
      simp only [ratioDelta, backRatio, forkRatio] at hdelta hj ⊢
      linarith

end TypeIIL

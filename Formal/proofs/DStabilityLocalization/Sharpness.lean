import proofs.DStabilityLocalization.Lifting
import proofs.DStabilityLocalization.Secant

/-!
# Sharpness of the localization dimension (L3), for every number of channels

The cyclic star `Cyc_k(ρ)` (`k = m + 2` channels): core `-I_k`, channel `c` reads
`x_{c+1}` and feeds `± ρ` into `x_c` (sign `-1` on the last channel only), one piece per
channel.  Its graph is a single negative-feedback cycle through `2k` first-order stages with
loop gain `g = ρ^k`.

* If `ρ cos²(π/2k) > 1` the star has strict growth (explicit eigenpair at unit rates).
* If `ρ^k cos(π/(2k-1))^(2k-1) < 1`, every boundary system with fewer than `k` synchronized
  groups is D-stable: a slow channel cuts the cycle, and otherwise the cycle has at most
  `2k - 1` lag stages, so the secant inequality excludes the closed right half-plane.
* Such `ρ` exist for every `k` (`cos_pow_strictMono`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Matrix Complex Set Real
open scoped BigOperators

namespace DStabilityLocalization
open DUnstableCores

variable (m : ℕ)

/-- Sign of the feedback of channel `c`: `-1` on the last channel. -/
def cycSgn (c : Fin (m + 2)) : ℝ := if c = Fin.last (m + 1) then -1 else 1

def cycB : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := fun i j => if i = j then -1 else 0

def cycU (c : Fin (m + 2)) (i : Fin (m + 2)) : ℝ := if i = c then cycSgn m c else 0

def cycV (c : Fin (m + 2)) (j : Fin (m + 2)) : ℝ := if j = c + 1 then 1 else 0

/-- The cyclic star with `m + 2` channels and equal loads `ρ`. -/
def cycStar (ρ : ℝ) : Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) ℝ :=
  star (cycB m) (cycU m) (cycV m) id (fun _ => ρ)

theorem cycSgn_sq (c : Fin (m + 2)) : cycSgn m c * cycSgn m c = 1 := by
  unfold cycSgn; split_ifs <;> norm_num

theorem prod_cycSgn : ∏ c : Fin (m + 2), (cycSgn m c : ℂ) = -1 := by
  rw [Fintype.prod_eq_single (Fin.last (m + 1)) (fun c hc => by simp [cycSgn, hc])]
  simp [cycSgn]

open Fin.NatCast Fin.CommRing in
/-- Backward propagation of zeros around the cycle. -/
theorem cyc_zero_all {x : Fin (m + 2) → ℂ} (hprop : ∀ c, x (c + 1) = 0 → x c = 0)
    {c₀ : Fin (m + 2)} (h0 : x c₀ = 0) : ∀ c, x c = 0 := by
  have hn : ∀ n : ℕ, x (c₀ - (n : Fin (m + 2))) = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      apply hprop
      have : c₀ - ((n + 1 : ℕ) : Fin (m + 2)) + 1 = c₀ - (n : Fin (m + 2)) := by
        push_cast; ring
      rw [this]; exact ih
  intro c
  have := hn (c₀ - c).val
  rwa [Fin.cast_val_eq_self, sub_sub_cancel] at this

/-! ### The rows of a boundary system of the cyclic star -/

/-- Effective channel value of a boundary system of the cyclic star. -/
def cycL (ρ : ℝ) (σ : Fin (m + 2) → Role) (t : Fin (m + 2) → ℝ) (z : ℂ) (c : Fin (m + 2)) : ℂ :=
  if σ c = Role.F then (ρ : ℂ) else if σ c = Role.D then (ρ : ℂ) / (1 + z * (t c : ℂ)) else 0

theorem sum_cycB (x : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    ∑ j, ((cycB m c j : ℝ) : ℂ) * x j = -x c := by
  rw [Fintype.sum_eq_single c (fun j hj => by simp [cycB, Ne.symm hj])]
  simp [cycB]

theorem sum_cycV (x : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    ∑ j, ((cycV m c j : ℝ) : ℂ) * x j = x (c + 1) := by
  rw [Fintype.sum_eq_single (c + 1) (fun j hj => by simp [cycV, hj])]
  simp [cycV]

theorem sum_cycU (f : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    ∑ c', f c' * ((cycU m c' c : ℝ) : ℂ) = f c * (cycSgn m c : ℂ) := by
  rw [Fintype.sum_eq_single c (fun c' hc' => by simp [cycU, Ne.symm hc'])]
  simp [cycU]

theorem cyc_bdCore_apply (ρ : ℝ) (σ : Fin (m + 2) → Role) (c j : Fin (m + 2)) :
    bdCore (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ c j =
      cycB m c j + (if σ c = Role.F then ρ * cycSgn m c * cycV m c j else 0) := by
  unfold bdCore
  congr 1
  rw [Fintype.sum_eq_single c (fun p hp => by simp [cycU, Ne.symm hp])]
  by_cases hF : σ c = Role.F <;> simp [cycU, hF]

theorem cyc_lag_apply (ρ : ℝ) (σ : Fin (m + 2) → Role) (t : Fin (m + 2) → ℝ) (z : ℂ)
    (c : Fin (m + 2)) : lagValue id (bdLoad id (fun _ => ρ) σ) t z c =
      if σ c = Role.D then (ρ : ℂ) / (1 + z * (t c : ℂ)) else 0 := by
  show (∑ p : Fin (m + 2), if p = c then (bdLoad id (fun _ => ρ) σ p : ℂ) /
    (1 + z * (t p : ℂ)) else 0) = _
  rw [Fintype.sum_eq_single c (fun x hx => if_neg hx), if_pos rfl]
  unfold bdLoad
  rw [Fintype.sum_eq_single c (fun p hp => by simp [id, hp])]
  by_cases hD : σ c = Role.D <;> simp [hD]

theorem cyc_row (ρ : ℝ) (σ : Fin (m + 2) → Role) (q t : Fin (m + 2) → ℝ) (z : ℂ)
    (x : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    (pencil (bdCore (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ) (cycU m) (cycV m) q
      (lagValue id (bdLoad id (fun _ => ρ) σ) t z) z *ᵥ x) c =
      (1 + z * (q c : ℂ)) * x c - (cycSgn m c : ℂ) * cycL m ρ σ t z c * x (c + 1) := by
  rw [pencil_mulVec]
  have hcore : (∑ j, ((bdCore (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ c j : ℝ) : ℂ) *
      x j) = -x c + (if σ c = Role.F then (ρ : ℂ) * cycSgn m c * x (c + 1) else 0) := by
    simp_rw [cyc_bdCore_apply]
    by_cases hF : σ c = Role.F
    · simp only [hF, if_true]
      push_cast
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [sum_cycB]
      have : ∑ j, (ρ : ℂ) * (cycSgn m c : ℂ) * (cycV m c j : ℂ) * x j =
          (ρ : ℂ) * (cycSgn m c : ℂ) * ∑ j, (cycV m c j : ℂ) * x j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, sum_cycV]
    · simp only [hF, if_false, add_zero]
      exact sum_cycB m x c
  have hchan : (∑ c', lagValue id (bdLoad id (fun _ => ρ) σ) t z c' * (cycU m c' c : ℂ) *
      ∑ j, (cycV m c' j : ℂ) * x j) =
      (if σ c = Role.D then (ρ : ℂ) / (1 + z * (t c : ℂ)) else 0) * cycSgn m c * x (c + 1) := by
    rw [Fintype.sum_eq_single c (fun c' hc' => by simp [cycU, Ne.symm hc'])]
    rw [cyc_lag_apply, sum_cycV]
    simp [cycU]
  rw [hcore, hchan]
  unfold cycL
  by_cases hF : σ c = Role.F
  · simp [hF]; ring
  · by_cases hD : σ c = Role.D
    · simp [hF, hD]; ring
    · simp [hF, hD]; ring

/-- **L3, lower boundary systems.** -/
theorem cyc_lower_dStable (ρ : ℝ) (hρ : 0 < ρ)
    (hsmall : ρ ^ (m + 2) * Real.cos (π / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1)
    (σ : Fin (m + 2) → Role) (hσ : ∃ c, σ c ≠ Role.D) :
    DStable (bdSystem (cycB m) (cycU m) (cycV m) id (fun _ => ρ) σ) := by
  intro d hd z y hy
  by_contra hz
  have hre : 0 ≤ z.re := not_lt.mp hz
  have hden : ∀ (t : ℝ), 0 ≤ t → 1 + z * (t : ℂ) ≠ 0 := by
    intro t ht h
    have := congrArg Complex.re h
    simp at this
    nlinarith [mul_nonneg hre ht]
  obtain ⟨x, hx, hker⟩ := pencil_kernel_of_eigenpair (bdCore (cycB m) (cycU m) (cycV m) id
    (fun _ => ρ) σ) (cycU m) (cycV m) id (bdLoad id (fun _ => ρ) σ) d hd z y hy
    (fun c => hden _ (inv_pos.mpr (hd _)).le)
  set q : Fin (m + 2) → ℝ := fun i => (d (.inl i))⁻¹
  set t : Fin (m + 2) → ℝ := fun c => (d (.inr c))⁻¹
  have hq : ∀ i, 0 < q i := fun i => inv_pos.mpr (hd _)
  have ht : ∀ c, 0 < t c := fun c => inv_pos.mpr (hd _)
  have hrow : ∀ c, (1 + z * (q c : ℂ)) * x c = (cycSgn m c : ℂ) * cycL m ρ σ t z c * x (c + 1) := by
    intro c
    have h := congrFun hker c
    rw [cyc_row] at h
    simpa [sub_eq_zero] using h
  have hprop : ∀ c, x (c + 1) = 0 → x c = 0 := by
    intro c h
    have := hrow c
    rw [h, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (hden _ (hq c).le)
  have hallne : ∀ c, x c ≠ 0 := by
    intro c h0
    exact hx (funext (cyc_zero_all m hprop h0))
  -- no slow channel
  have hnoS : ∀ c, σ c ≠ Role.S := by
    intro c hS
    have := hrow c
    have hL : cycL m ρ σ t z c = 0 := by simp [cycL, hS]
    rw [hL, mul_zero, zero_mul] at this
    exact hallne c ((mul_eq_zero.mp this).resolve_left (hden _ (hq c).le))
  -- product around the cycle
  have hprod : (∏ c, (1 + z * (q c : ℂ))) * ∏ c, x c =
      (∏ c, (cycSgn m c : ℂ)) * (∏ c, cycL m ρ σ t z c) * ∏ c, x c := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun c _ => hrow c),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun c => rfl)
  have hxprod : (∏ c, x c) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hallne c)
  have hprod' : (∏ c, (1 + z * (q c : ℂ))) = -(∏ c, cycL m ρ σ t z c) := by
    have := mul_right_cancel₀ hxprod hprod
    rw [this, prod_cycSgn]; ring
  -- clear the lags of the synchronized channels
  have hLD : ∀ c, cycL m ρ σ t z c * (if σ c = Role.D then 1 + z * (t c : ℂ) else 1) =
      (ρ : ℂ) := by
    intro c
    unfold cycL
    by_cases hF : σ c = Role.F
    · simp [hF]
    · have hD : σ c = Role.D := by
        cases h : σ c
        · exact absurd h hF
        · exact absurd h (hnoS c)
        · rfl
      simp [hD]
      field_simp [hden _ (ht c).le]
  have hfull : (∏ c, (1 + z * (q c : ℂ))) *
      ∏ c ∈ Finset.univ.filter (fun c => σ c = Role.D), (1 + z * (t c : ℂ)) =
      -((ρ ^ (m + 2) : ℝ) : ℂ) := by
    rw [Finset.prod_filter, hprod']
    have : (∏ c, cycL m ρ σ t z c) * ∏ c, (if σ c = Role.D then 1 + z * (t c : ℂ) else 1) =
        ∏ _c : Fin (m + 2), (ρ : ℂ) := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl (fun c _ => hLD c)
    rw [neg_mul, this]
    simp
  -- apply the secant inequality to the combined index set
  set Dset := Finset.univ.filter (fun c => σ c = Role.D)
  let τ : Fin (m + 2) ⊕ Fin (m + 2) → ℝ := Sum.elim q t
  have hsec := secant_inequality (Finset.univ.disjSum Dset) τ
    (fun j _ => by rcases j with i | c; exact hq i; exact ht c) z hre (ρ ^ (m + 2))
    (pow_pos hρ _) (by
      rw [Finset.prod_disjSum]
      simpa [τ] using hfull)
  obtain ⟨h3, hineq⟩ := hsec
  rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at h3 hineq
  -- at most `k - 1` synchronized channels
  obtain ⟨c₀, hc₀⟩ := hσ
  have hDcard : Dset.card < m + 2 := by
    have : Dset ⊂ Finset.univ := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun h => ?_⟩
      have : c₀ ∈ Dset := by rw [h]; exact Finset.mem_univ _
      simp [Dset] at this
      exact hc₀ this
    simpa using Finset.card_lt_card this
  have hN : m + 2 + Dset.card ≤ 2 * (m + 2) - 1 := by omega
  have hmono : Real.cos (π / (m + 2 + Dset.card : ℕ)) ^ (m + 2 + Dset.card) ≤
      Real.cos (π / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) := by
    rcases hN.lt_or_eq with hlt | heq
    · exact (cos_pow_strictMono h3 hlt).le
    · rw [heq]
  have hpos : 0 ≤ ρ ^ (m + 2) := (pow_pos hρ _).le
  have := mul_le_mul_of_nonneg_left hmono hpos
  push_cast at hineq this
  linarith

theorem cycStar_mulVec_inl (ρ : ℝ) (x w : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    (complexify (rightScale (cycStar m ρ) (fun _ => 1)) *ᵥ Sum.elim x w) (.inl c) =
      -x c + (ρ : ℂ) * cycSgn m c * w c := by
  rw [cycStar, star_mulVec_inl]
  simp only [Complex.ofReal_one, one_mul, Sum.elim_inl, Sum.elim_inr, id]
  rw [sum_cycB]
  have : ∑ p, (ρ : ℂ) * (cycU m p c : ℂ) * w p = ∑ p, ((ρ : ℂ) * w p) * (cycU m p c : ℂ) :=
    Finset.sum_congr rfl (fun p _ => by ring)
  rw [this, sum_cycU]
  ring

theorem cycStar_mulVec_inr (ρ : ℝ) (x w : Fin (m + 2) → ℂ) (c : Fin (m + 2)) :
    (complexify (rightScale (cycStar m ρ) (fun _ => 1)) *ᵥ Sum.elim x w) (.inr c) =
      x (c + 1) - w c := by
  rw [cycStar, star_mulVec_inr]
  simp only [Complex.ofReal_one, one_mul, Sum.elim_inl, Sum.elim_inr, id]
  rw [sum_cycV]

/-- The explicit eigenvalue `√ρ e^{iπ/2k} - 1` of `Cyc_k(ρ)` at unit rates (`k = m + 2`). -/
def cycEig (ρ : ℝ) : ℂ :=
  (Real.sqrt ρ : ℂ) * Complex.exp (((π / (2 * ((m : ℝ) + 2))) : ℝ) * I) - 1

theorem cycEig_re (ρ : ℝ) :
    (cycEig m ρ).re = Real.sqrt ρ * Real.cos (π / (2 * ((m : ℝ) + 2))) - 1 := by
  rw [cycEig, Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- **L3, explicit eigenpair of the full star at unit rates.** -/
theorem cyc_star_eigenpair (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ y, HasEigenpair (rightScale (cycStar m ρ) (fun _ => 1)) (cycEig m ρ) y := by
  have hk0 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hkR : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  set ζ : ℂ := Complex.exp (((π / ((m : ℝ) + 2)) : ℝ) * I) with hζ
  set μ : ℂ := (Real.sqrt ρ : ℂ) * Complex.exp (((π / (2 * ((m : ℝ) + 2))) : ℝ) * I) with hμ
  have hsq : (Real.sqrt ρ : ℂ) ^ 2 = ρ := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hρ.le]
  have hμsq : μ ^ 2 = (ρ : ℂ) * ζ := by
    rw [hμ, hζ, mul_pow, hsq, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    field_simp
  have hζk : ζ ^ (m + 2) = -1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : ((m + 2 : ℕ) : ℂ) * (((π / ((m : ℝ) + 2) : ℝ) : ℂ) * I) = π * I := by
      push_cast
      have : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast hkR.ne'
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have hμne : μ ≠ 0 := by
    rw [hμ]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    exact_mod_cast (Real.sqrt_pos.mpr hρ).ne'
  set x : Fin (m + 2) → ℂ := fun c => ζ ^ c.val with hx
  set w : Fin (m + 2) → ℂ := fun c => x (c + 1) / μ with hw
  have key : ∀ c : Fin (m + 2), (ρ : ℂ) * (cycSgn m c : ℂ) * x (c + 1) = μ ^ 2 * x c := by
    intro c
    rw [hμsq]
    by_cases hc : c = Fin.last (m + 1)
    · subst hc
      simp only [cycSgn, if_true, hx, Fin.last_add_one, Fin.val_zero, pow_zero, Fin.val_last]
      push_cast
      have : ζ * ζ ^ (m + 1) = ζ ^ (m + 2) := by ring
      rw [mul_assoc (ρ : ℂ) ζ, this, hζk]
      ring
    · have hlt : c < Fin.last (m + 1) := lt_of_le_of_ne (Fin.le_last c) hc
      simp only [cycSgn, hc, if_false, hx, Fin.val_add_one_of_lt hlt, pow_succ]
      push_cast
      ring
  rw [show cycEig m ρ = μ - 1 from rfl]
  refine ⟨Sum.elim x w, ?_, ?_⟩
  · intro h0
    have := congrFun h0 (.inl 0)
    simp [hx] at this
  · intro a
    rcases a with c | c
    · rw [cycStar_mulVec_inl]
      simp only [Sum.elim_inl, hw]
      field_simp
      linear_combination key c
    · rw [cycStar_mulVec_inr]
      simp only [Sum.elim_inr, hw]
      field_simp

/-- The explicit eigenvalue lies in the open right half-plane when `ρ cos²(π/2k) > 1`. -/
theorem cycEig_re_pos (ρ : ℝ) (hρ : 0 < ρ)
    (hbig : 1 < ρ * Real.cos (π / (2 * (m + 2))) ^ 2) : 0 < (cycEig m ρ).re := by
  rw [cycEig_re]
  have hc : 0 < Real.cos (π / (2 * ((m : ℝ) + 2))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / (2 * ((m : ℝ) + 2)) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]
  have h1 : 1 < (Real.sqrt ρ * Real.cos (π / (2 * ((m : ℝ) + 2)))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hρ.le]
    exact hbig
  have h2 : 0 < Real.sqrt ρ * Real.cos (π / (2 * ((m : ℝ) + 2))) :=
    mul_pos (Real.sqrt_pos.mpr hρ) hc
  nlinarith

/-- **L3, the full star is unstable.** -/
theorem cyc_star_dUnstable (ρ : ℝ) (hρ : 0 < ρ)
    (hbig : 1 < ρ * Real.cos (π / (2 * (m + 2))) ^ 2) : DUnstable (cycStar m ρ) := by
  obtain ⟨y, hy⟩ := cyc_star_eigenpair m ρ hρ
  exact ⟨fun _ => 1, fun _ => one_pos, cycEig m ρ, y, cycEig_re_pos m ρ hρ hbig, hy⟩

/-- The secant window is nonempty for every `k = m + 2`. -/
theorem cyc_window : ∃ ρ : ℝ, 0 < ρ ∧ 1 < ρ * Real.cos (π / (2 * (m + 2))) ^ 2 ∧
    ρ ^ (m + 2) * Real.cos (π / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) < 1 := by
  have hcast : ((2 * (m + 2) : ℕ) : ℝ) = 2 * ((m : ℝ) + 2) := by push_cast; ring
  set a : ℝ := Real.cos (π / (2 * ((m : ℝ) + 2))) ^ (2 * (m + 2)) with ha_def
  set b : ℝ := Real.cos (π / (2 * (m + 2) - 1 : ℕ)) ^ (2 * (m + 2) - 1) with hb_def
  have hab : b < a := by
    have := cos_pow_strictMono (M := 2 * (m + 2) - 1) (N := 2 * (m + 2)) (by omega) (by omega)
    rw [hcast] at this
    exact this
  have hc : 0 < Real.cos (π / (2 * ((m : ℝ) + 2))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / (2 * ((m : ℝ) + 2)) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_pos]
  have ha : 0 < a := pow_pos hc _
  have hb0 : 0 ≤ b := by
    have h3 : (3 : ℝ) ≤ ((2 * (m + 2) - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 3 ≤ 2 * (m + 2) - 1)
    have : 0 < Real.cos (π / (2 * (m + 2) - 1 : ℕ)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 < π / ((2 * (m + 2) - 1 : ℕ) : ℝ) := by
          apply div_pos Real.pi_pos; linarith
        linarith [Real.pi_pos]
      · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
        nlinarith [Real.pi_pos]
    exact (pow_pos this _).le
  set G : ℝ := 2 / (a + b) with hG
  have hGpos : 0 < G := by positivity
  set ρ : ℝ := G ^ ((1 : ℝ) / ((m : ℝ) + 2)) with hρ_def
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hGpos _
  have hρk : ρ ^ (m + 2) = G := by
    rw [hρ_def, ← Real.rpow_natCast, ← Real.rpow_mul hGpos.le]
    have : (1 : ℝ) / ((m : ℝ) + 2) * ((m + 2 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  refine ⟨ρ, hρpos, ?_, ?_⟩
  · have hGa : 1 < G * a := by
      rw [hG, div_mul_eq_mul_div, one_lt_div (by positivity)]; linarith
    have h1 : 1 < (ρ * Real.cos (π / (2 * ((m : ℝ) + 2))) ^ 2) ^ (m + 2) := by
      have e : (ρ * Real.cos (π / (2 * ((m : ℝ) + 2))) ^ 2) ^ (m + 2) = G * a := by
        rw [mul_pow, hρk, ← pow_mul, ha_def]
      rw [e]; exact hGa
    by_contra hle
    push Not at hle
    have h0 : 0 ≤ ρ * Real.cos (π / (2 * ((m : ℝ) + 2))) ^ 2 := by positivity
    have := pow_le_one₀ h0 hle (n := m + 2)
    linarith
  · rw [hρk]
    have : G * b < 1 := by
      rw [hG, div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
    exact this

end DStabilityLocalization

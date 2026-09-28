import proofs.DStabilityHardness.CertificatesTimeScale
import proofs.DStabilityHardness.Main

/-!
# The time-scale cost of instability in the hard instances

Every positive scaling of a Pell star matrix (core `coreB (p/q) (hv (p/q) + 1/2)`, any positive
loads of total `1`) that has an eigenvalue with nonnegative real part runs the port faster than the
**sum** of the three inner rates by a factor `> q²`.  For the reduction (`q ≥ 8T`) every
destabilizing scaling therefore has time-scale ratio `> 64 T²`.

Proof: absorption turns the eigenvalue into a closed-right-half-plane eigenvalue of a static load
point with a port rate no larger than the original one; the quartic Routh–Hurwitz criterion forces
`Δ₃ ≤ 0`; the Hurwitz decomposition gives `F₂ < h (-K) r v`; the certificate `F₂ ≥ 200 p r` and the
window bound `-K ≤ k₂ W = O(1/q²)` finish.
-/

namespace DStabilityHardness

open DUnstableCores CollectiveInstability DStabilityCharacterization.Granularity
open scoped BigOperators

noncomputable section

theorem F2c_nonneg {ρ h x y z : ℝ} (hρ0 : 17 / 10 ≤ ρ) (hρ1 : ρ ≤ 7 / 4) (hh0 : 3 ≤ h)
    (hh1 : h ≤ 5) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 0 ≤ F2c ρ h x y z :=
  sym_nonneg (F2c ρ h)
    (fun x y z => by unfold F2c F2; rw [sp_12, sq_12, sr_12])
    (fun x y z => by unfold F2c F2; rw [sp_23, sq_23, sr_23])
    (fun A B C hA hB hC => F2c_ordered_nonneg ρ h A B C hρ0 hρ1 hh0 hh1 hA hB hC) x y z hx hy hz

theorem load_bounds_closed {z : ℂ} (hz : 0 ≤ z.re) {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    0 < staticLoad z r t ∧ staticLoad z r t ≤ r := by
  by_cases hz0 : z = 0
  · subst hz0
    simp [staticLoad, denom, hr]
  · have := load_bounds hz hz0 hr ht
    exact ⟨this.1, this.2.le⟩

/-- The scalar arithmetic of the time-scale bound, isolated from the matrix context. -/
theorem port_rate_arith (h K W k2 F0 F1 F2 mU sp sr vp qq : ℝ)
    (hΔ : F0 + F1 * vp + F2 * vp ^ 2 + h * (mU + K * sr) * vp ^ 3 ≤ 0)
    (hF0 : 0 < F0) (hF1 : 0 ≤ F1) (hmU : 0 ≤ mU) (hF2 : 200 * sp * sr ≤ F2)
    (hh : 0 < h) (hh5 : h ≤ 5) (hsp : 0 < sp) (hsr : 0 < sr) (hvp : 0 < vp)
    (hK : -K ≤ k2 * W) (hk2 : 0 < k2) (hk2' : k2 ≤ 11 / 2) (hW : W ≤ 2304 / 625 * (1 / qq))
    (hqq : 0 < qq) : qq * sp < vp := by
  have e1 : h * (mU + K * sr) * vp ^ 3 = h * mU * vp ^ 3 + h * K * sr * vp ^ 3 := by ring
  rw [e1] at hΔ
  have t1 : 0 ≤ F1 * vp := mul_nonneg hF1 hvp.le
  have t2 : 0 ≤ h * mU * vp ^ 3 := by positivity
  have s1 : F2 * vp ^ 2 < -(h * K * sr * vp ^ 3) := by linarith
  have s2 : 200 * sp * sr * vp ^ 2 ≤ F2 * vp ^ 2 := mul_le_mul_of_nonneg_right hF2 (by positivity)
  have hsv : 0 < sr * vp ^ 2 := by positivity
  have s3 : (200 * sp) * (sr * vp ^ 2) < (-(h * K) * vp) * (sr * vp ^ 2) := by
    have e2 : (200 * sp) * (sr * vp ^ 2) = 200 * sp * sr * vp ^ 2 := by ring
    have e3 : (-(h * K) * vp) * (sr * vp ^ 2) = -(h * K * sr * vp ^ 3) := by ring
    rw [e2, e3]; linarith
  have s4 : 200 * sp < -(h * K) * vp := lt_of_mul_lt_mul_right s3 hsv.le
  have hKpos : 0 < -K := by
    by_contra hc
    push Not at hc
    have : 0 ≤ h * K * vp := mul_nonneg (mul_nonneg hh.le (by linarith)) hvp.le
    have : -(h * K) * vp = -(h * K * vp) := by ring
    linarith
  have hWpos : 0 < W := by
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hk2.le hc
    linarith
  have s5 : -K ≤ 11 / 2 * (2304 / 625 * (1 / qq)) := by
    calc -K ≤ k2 * W := hK
      _ ≤ 11 / 2 * W := mul_le_mul_of_nonneg_right hk2' hWpos.le
      _ ≤ 11 / 2 * (2304 / 625 * (1 / qq)) := by linarith
  have s6 : -(h * K) * vp ≤ 5 * (11 / 2 * (2304 / 625 * (1 / qq))) * vp := by
    have e : -(h * K) * vp = (h * (-K)) * vp := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hvp.le
    exact mul_le_mul hh5 s5 hKpos.le (by norm_num)
  have s7 : 200 * sp < 12672 / 125 * vp / qq := by
    have e : 5 * (11 / 2 * (2304 / 625 * (1 / qq))) * vp = 12672 / 125 * vp / qq := by
      field_simp; ring
    linarith
  rw [lt_div_iff₀ hqq] at s7
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Time-scale lower bound.** A scaling with a closed-right-half-plane eigenvalue runs the port
faster than `q²` times the sum of the inner rates. -/
theorem destabilizing_port_fast {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq4 : 4 ≤ q)
    (r : κ → ℝ) (hr : ∀ j, 0 < r j) (hG : ∑ j, r j = 1)
    (d : Fin 4 ⊕ κ → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (u : Fin 4 ⊕ κ → ℂ) (hz : 0 ≤ z.re)
    (hu : HasEigenpair
      (rightScale (attached (coreB ((p : ℝ) / q) (hv ((p : ℝ) / q) + 1 / 2)) port r) d) z u) :
    (q : ℝ) ^ 2 * (d (.inl 0) + d (.inl 1) + d (.inl 2)) < d (.inl port) := by
  obtain ⟨hsq, hρ0, hρ1⟩ := pell_facts p q hpell hq4
  set ρ := (p : ℝ) / q with hρdef
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨hn, hc, hl⟩ := attached_pencil _ _ _ d hd z u hu
  let qi : Fin 4 → ℝ := fun i => (d (.inl i))⁻¹
  let t : κ → ℝ := fun j => (d (.inr j))⁻¹
  have hqi : ∀ i, 0 < qi i := fun i => inv_pos.mpr (hd _)
  have ht : ∀ j, 0 < t j := fun j => inv_pos.mpr (hd _)
  obtain ⟨hv0, hst⟩ := attached_static (coreB ρ (hv ρ + 1 / 2)) port r qi t hqi ht z hz _ _ hn hc hl
  set v : Fin 4 → ℂ := fun i => (d (.inl i) : ℂ) * u (.inl i)
  set X : ℝ := ∑ k, staticLoad z (r k) (t k) with hXdef
  set a : ℝ := ∑ k, lagShift z (r k) (t k) with hadef
  have hX0 : 0 < X := Finset.sum_pos (fun j _ => (load_bounds_closed hz (hr j) (ht j)).1)
    Finset.univ_nonempty
  have hX1 : X ≤ 1 := by
    rw [← hG]; exact Finset.sum_le_sum (fun j _ => (load_bounds_closed hz (hr j) (ht j)).2)
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun j _ => (shift_pos hz (hr j) (ht j)).le)
  let q' : Fin 4 → ℝ := fun i => qi i + if i = port then a else 0
  have hq' : ∀ i, 0 < q' i := by
    intro i; dsimp only [q']; split_ifs <;> linarith [hqi i]
  obtain ⟨hvb0, hvb1⟩ := hv_bounds hρ0 hρ1
  set h := hv ρ + 1 / 2 - X with hhdef
  have hb : InBox ρ h := ⟨hρ0, hρ1, by linarith, by linarith⟩
  have he' : ∀ i, ∑ j, (coreB ρ h i j : ℂ) * v j = z * (q' i : ℂ) * v i := by
    intro i; rw [hhdef, ← loadCore_coreB]; exact hst i
  have heig := eigenpair_of_pencil (coreB ρ h) q' hq' z v hv0 he'
  -- the static rates
  set x0 := (q' 0)⁻¹; set x1 := (q' 1)⁻¹; set x2 := (q' 2)⁻¹; set vp := (q' 3)⁻¹
  have hx0 : x0 = d (.inl 0) := by simp [x0, q', qi, port]
  have hx1 : x1 = d (.inl 1) := by simp [x1, q', qi, port]
  have hx2 : x2 = d (.inl 2) := by simp [x2, q', qi, port]
  have hvp : vp ≤ d (.inl port) := by
    have e : q' 3 = qi 3 + a := by simp [q', port]
    change (q' 3)⁻¹ ≤ d (.inl port)
    rw [e]
    have h1 : qi 3 ≤ qi 3 + a := by linarith
    have h2 := inv_anti₀ (hqi 3) h1
    have h3 : (qi 3)⁻¹ = d (.inl port) := by simp [qi, port]
    linarith
  have hxpos : 0 < x0 ∧ 0 < x1 ∧ 0 < x2 ∧ 0 < vp :=
    ⟨inv_pos.mpr (hq' 0), inv_pos.mpr (hq' 1), inv_pos.mpr (hq' 2), inv_pos.mpr (hq' 3)⟩
  obtain ⟨px0, px1, px2, pvp⟩ := hxpos
  rw [vec4_eta (fun i => (q' i)⁻¹)] at heig
  change HasEigenpair (rightScale (coreB ρ h) ![x0, x1, x2, vp]) z _ at heig
  -- not Hurwitz, hence Δ₃ ≤ 0
  obtain ⟨c1p, c2p, c3p, c4p⟩ := coeffs_pos hb px0 px1 px2 pvp
  have hΔ : hurwitzDelta (c1 ρ h x0 x1 x2 vp) (c2 ρ h x0 x1 x2 vp) (c3 ρ h x0 x1 x2 vp)
      (c4 ρ h x0 x1 x2 vp) ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have := matrix_hurwitzStable_of_delta_pos (scaled_charpoly ρ h x0 x1 x2 vp) c1p c2p c3p c4p
      hpos z _ heig
    linarith
  rw [delta3_decomposition] at hΔ
  have hh : 0 < h := by linarith [hb.h0]
  have hr3 : 0 < sr x0 x1 x2 := by unfold sr; positivity
  have hp3 : 0 < sp x0 x1 x2 := by unfold sp; positivity
  have h0 := F0_pos (x := x0) (y := x1) (z := x2) hρ0 hρ1 px0 px1 px2
  have h1 := F1_nonneg hρ0 hρ1 hb.h0 hb.h1 px0.le px1.le px2.le
  have h2c := F2c_nonneg hρ0 hρ1 hb.h0 hb.h1 px0.le px1.le px2.le
  have hU := U_nonneg px0.le px1.le px2.le
  have hm2 := m2_pos hb.h0; have hm3 := m3_pos hρ0 hb.h0
  have hk := k2_pos hρ0 hρ1
  unfold F2c at h2c
  -- F₂ v² < -h K r v³
  have hmU0 : 0 ≤ m2 h * m3 ρ h * U x0 x1 x2 := by positivity
  have hK : -Kf ρ h ≤ k2 ρ * Wd ρ := by
    rw [Kf_window ρ h hk]
    have := mul_nonneg hk.le (sq_nonneg (h - hv ρ))
    have e : -(k2 ρ * ((h - hv ρ) ^ 2 - Wd ρ)) = k2 ρ * Wd ρ - k2 ρ * (h - hv ρ) ^ 2 := by ring
    rw [e]; linarith
  have h3 : 3 ≤ ρ ^ 2 := by
    rw [hsq]; linarith [(by positivity : (0 : ℝ) < 1 / (q : ℝ) ^ 2)]
  have hW := Wd_le hρ0 le_rfl hρ1 h3
  have hW' : Wd ρ ≤ 2304 / 625 * (1 / (q : ℝ) ^ 2) := by
    have e : ρ ^ 2 - 3 = 1 / (q : ℝ) ^ 2 := by rw [hsq]; ring
    rw [e] at hW; exact hW
  have hk2 : k2 ρ ≤ 11 / 2 := by unfold k2; nlinarith
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  have key := port_rate_arith h (Kf ρ h) (Wd ρ) (k2 ρ) (F0 ρ x0 x1 x2) (F1 ρ h x0 x1 x2)
    (F2 ρ h x0 x1 x2) (m2 h * m3 ρ h * U x0 x1 x2) (sp x0 x1 x2) (sr x0 x1 x2) vp ((q : ℝ) ^ 2)
    hΔ h0 h1 hmU0 (by linarith) hh hb.h1 hp3 hr3 pvp hK hk hk2 hW' hq2
  have hsp : sp x0 x1 x2 = d (.inl 0) + d (.inl 1) + d (.inl 2) := by
    unfold sp; rw [hx0, hx1, hx2]
  rw [hsp] at key
  linarith

/-- For the reduction's matrices: every scaling exhibiting instability has time-scale ratio
(port rate over any inner rate) greater than `64 T²`. -/
theorem hard_instances_spread {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (w : κ → ℕ) (hw : ∀ j, 0 < w j) (T : ℕ) (hT : ∑ j, w j = 2 * T)
    (p q : ℕ) (hpell : p ^ 2 = 3 * q ^ 2 + 1) (hq : 8 * T ≤ q) (hq4 : 4 ≤ q)
    (d : Fin 4 ⊕ κ → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (u : Fin 4 ⊕ κ → ℂ) (hz : 0 ≤ z.re)
    (hu : HasEigenpair (rightScale (hardMatrix p q w T) d) z u) (i : Fin 4) (hi : i ≠ port) :
    64 * (T : ℝ) ^ 2 * d (.inl i) < d (.inl port) := by
  obtain ⟨j0⟩ := (inferInstance : Nonempty κ)
  have hTpos : 0 < T := by
    have : w j0 ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j0)
    have := hw j0; omega
  have hr : ∀ j, 0 < hardLoads w T j := by
    intro j; unfold hardLoads
    have : (0 : ℝ) < w j := by exact_mod_cast hw j
    have : (0 : ℝ) < T := by exact_mod_cast hTpos
    positivity
  have hG : ∑ j, hardLoads w T j = 1 := by
    unfold hardLoads; rw [← Finset.sum_div]
    have : (∑ j, (w j : ℝ)) = 2 * T := by exact_mod_cast hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
    rw [this]; field_simp
  have key := destabilizing_port_fast p q hpell hq4 (hardLoads w T) hr hG d hd z u hz hu
  have hq8 : (8 : ℝ) * T ≤ q := by exact_mod_cast hq
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have h64 : 64 * (T : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
  have hsum : d (.inl i) ≤ d (.inl 0) + d (.inl 1) + d (.inl 2) := by
    have h0 := hd (.inl 0); have h1 := hd (.inl 1); have h2 := hd (.inl 2)
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by
      fin_cases i <;> simp [port] at hi ⊢
    rcases hcases with rfl | rfl | rfl <;> linarith
  have hdi := hd (.inl i)
  calc 64 * (T : ℝ) ^ 2 * d (.inl i) ≤ (q : ℝ) ^ 2 * d (.inl i) :=
        mul_le_mul_of_nonneg_right h64 hdi.le
    _ ≤ (q : ℝ) ^ 2 * (d (.inl 0) + d (.inl 1) + d (.inl 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ < d (.inl port) := key

end

end DStabilityHardness

import proofs.SpecimenReliability.AtLeastOneGate

namespace SpecimenReliability
noncomputable section

def gateCurve (m : ℕ) (H z : ℝ) : ℝ := z^m*(1-z*(1-H))
def gateOpt (m : ℕ) (H : ℝ) : ℝ :=
  if 1 ≤ (m+1:ℝ)*H then 1 else (m:ℝ)/((m+1:ℝ)*(1-H))
def gateBound (m : ℕ) (H : ℝ) : ℝ := gateCurve m H (gateOpt m H)

theorem gate_derivative (m : ℕ) (H z : ℝ) :
    HasDerivAt (gateCurve (m+1) H)
      (z^m*((m+1:ℝ)-(m+2:ℝ)*(1-H)*z)) z := by
  have h := (hasDerivAt_pow (m+1) z).mul
    ((hasDerivAt_const z 1).sub ((hasDerivAt_id z).mul_const (1-H)))
  convert h using 1
  simp [Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem curve_le_peak (m : ℕ) (H b z : ℝ) (hH : H ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (hleft : 0 ≤ (m+1:ℝ)-(m+2:ℝ)*(1-H)*b)
    (hright : b=1 ∨ (m+1:ℝ)-(m+2:ℝ)*(1-H)*b ≤ 0) :
    gateCurve (m+1) H z ≤ gateCurve (m+1) H b := by
  have hc : 0 ≤ (m+2:ℝ)*(1-H) := mul_nonneg (by positivity) (by linarith)
  have hcont : Continuous (gateCurve (m+1) H) := by unfold gateCurve; fun_prop
  by_cases hzb : z ≤ b
  · have hmono : MonotoneOn (gateCurve (m+1) H) (Set.Icc 0 b) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b) hcont.continuousOn
        (fun x _ => (gate_derivative m H x).hasDerivWithinAt)
      intro x hx
      have hi := interior_subset hx
      have hxb : x ≤ b := hi.2
      exact mul_nonneg (pow_nonneg hi.1 m) (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hxb)])
    exact hmono ⟨hz.1,hzb⟩ ⟨hb.1,le_rfl⟩ hzb
  · have hbz : b ≤ z := le_of_lt (lt_of_not_ge hzb)
    have hr : (m+1:ℝ)-(m+2:ℝ)*(1-H)*b ≤ 0 := by
      rcases hright with he | he
      · exfalso; apply hzb; simpa [he] using hz.2
      · exact he
    have hanti : AntitoneOn (gateCurve (m+1) H) (Set.Icc b 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc b 1) hcont.continuousOn
        (fun x _ => (gate_derivative m H x).hasDerivWithinAt)
      intro x hx
      have hi := interior_subset hx
      have hxb : b ≤ x := hi.1
      exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_trans hb.1 hxb) m)
        (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hxb)])
    exact hanti ⟨le_rfl,hb.2⟩ ⟨hbz,hz.2⟩ hbz

theorem gate_opt_properties (m : ℕ) (hm : 1 ≤ m) (H : ℝ) (hH : 0 ≤ H ∧ H ≤ 1) :
    (0 ≤ gateOpt m H ∧ gateOpt m H ≤ 1) ∧
    0 ≤ (m:ℝ)-(m+1:ℝ)*(1-H)*gateOpt m H ∧
    (gateOpt m H=1 ∨ (m:ℝ)-(m+1:ℝ)*(1-H)*gateOpt m H ≤ 0) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  unfold gateOpt
  split_ifs with h
  · refine ⟨by norm_num, ?_, Or.inl rfl⟩
    nlinarith
  · have hd : 0 < (m+1:ℝ)*(1-H) := by
      have hlt : H < 1 := by nlinarith
      positivity
    have he : (m:ℝ)-(m+1:ℝ)*(1-H)*((m:ℝ)/((m+1:ℝ)*(1-H))) = 0 := by
      have hh : 1-H ≠ 0 := by intro hh; rw [hh, mul_zero] at hd; exact lt_irrefl _ hd
      have hn : (m+1:ℝ) ≠ 0 := by positivity
      field_simp [hh,hn]
      ring
    refine ⟨⟨le_of_lt (div_pos hm0 hd), (div_le_one hd).2 (by nlinarith)⟩, ?_, Or.inr ?_⟩
    · rw [he]
    · rw [he]

theorem gate_maximum (m : ℕ) (hm : 1 ≤ m) (H z : ℝ)
    (hH : 0 ≤ H ∧ H ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    gateCurve m H z ≤ gateBound m H := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨hb,hl,hr⟩ := gate_opt_properties (j+1) hm H hH
  simp only [Nat.cast_add, Nat.cast_one] at hl hr
  have hl' : 0 ≤ (j+1:ℝ)-(j+2:ℝ)*(1-H)*gateOpt (j+1) H := by convert hl using 1; ring
  have hr' : gateOpt (j+1) H=1 ∨ (j+1:ℝ)-(j+2:ℝ)*(1-H)*gateOpt (j+1) H ≤ 0 := by
    convert hr using 1; ring
  exact curve_le_peak j H _ z hH.2 hb hz hl' hr'

theorem gate_endpoint (m : ℕ) (H : ℝ) (h : 1 ≤ (m+1:ℝ)*H) :
    gateBound m H = H := by simp [gateBound,gateOpt,h,gateCurve]

theorem accepted_general {S : Type*} [Fintype S] (μ x y : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hs : ∑ s, μ s = 1)
    (hx : ∀ s, 0 ≤ x s ∧ x s ≤ 1) (hy : ∀ s, 0 ≤ y s ∧ y s ≤ 1)
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) (k n m : ℕ) (hkn : k ≤ n) (hm : 1 ≤ m) :
    acceptedRisk μ x y a a n m ≤ gateBound m ((1-a)^k) := by
  obtain ⟨hq,hp,hr,hl⟩ := moments_feasible μ x y hμ hs hx hy
  have hw := acceptance_interval _ _ _ hq hp hr hl
  have hH : 0 ≤ (1-a)^k ∧ (1-a)^k ≤ 1 :=
    ⟨pow_nonneg (by linarith) k, pow_le_one₀ (by linarith) (by linarith)⟩
  exact (accepted_reduction μ x y hμ hs hx hy a ha ha' k n m hkn).trans
    (gate_maximum m hm _ _ hH hw)

theorem general_attainment (a : ℝ) (k m : ℕ) :
    acceptedRisk (corners (gateOpt m ((1-a)^k)/2) (gateOpt m ((1-a)^k)/2) 0)
      cornerX cornerY a a k m = gateBound m ((1-a)^k) := by
  rw [accepted_witness]
  rfl

end
end SpecimenReliability


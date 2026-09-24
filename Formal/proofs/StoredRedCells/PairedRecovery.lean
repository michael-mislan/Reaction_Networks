import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! Conditional paired-signal identification. Oxidation q is time-varying.
The common reduction coefficient and proportional treatment input are explicit
model assumptions, not conclusions about CO or a human preparation. -/
namespace StoredRedCells.PairedRecovery
noncomputable section

theorem paired_cancellation (D C q k : ℝ → ℝ) (r t : ℝ)
    (hD : HasDerivAt D (q t - k t * D t) t)
    (hC : HasDerivAt C (r * q t - k t * C t) t) :
    HasDerivAt (fun s => C s - r * D s) (-k t * (C t - r * D t)) t := by
  convert hC.sub (hD.const_mul r) using 1
  ring

theorem paired_discrepancy (D C q k eta delta : ℝ → ℝ) (r t : ℝ)
    (hD : HasDerivAt D (q t - k t * D t) t)
    (hC : HasDerivAt C (r * q t + eta t - (k t + delta t) * C t) t) :
    HasDerivAt (fun s => C s - r * D s)
      (-k t * (C t - r * D t) + eta t - delta t * C t) t := by
  convert hC.sub (hD.const_mul r) using 1
  ring

/-- Integrating-factor identity for continuous effective reduction and arbitrary
oxidation compatible with the two differentiable signals. Global hypotheses
are an explicit first formalization scope. No constant-q assumption is used. -/
theorem paired_integrated_identity (D C q k : ℝ → ℝ) (r D0 t : ℝ)
    (hk : Continuous k) (hD0 : D 0 = D0) (hC0 : C 0 = D0)
    (hD : ∀ s, HasDerivAt D (q s - k s * D s) s)
    (hC : ∀ s, HasDerivAt C (r * q s - k s * C s) s) :
    C t - r * D t = (1-r)*D0 * Real.exp (-(∫ s in (0:ℝ)..t, k s)) := by
  let K : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, k s
  have hK (u : ℝ) : HasDerivAt K (k u) u :=
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  let F : ℝ → ℝ := fun u => Real.exp (K u) * (C u-r*D u)
  have hF (u : ℝ) : HasDerivAt F 0 u := by
    convert (hK u).exp.mul (paired_cancellation D C q k r u (hD u) (hC u)) using 1
    dsimp [F]
    ring
  have hconst : F t = F 0 :=
    is_const_of_deriv_eq_zero (fun u => (hF u).differentiableAt)
      (fun u => (hF u).deriv) t 0
  have he : Real.exp (K t) * (C t-r*D t) = (1-r)*D0 := by
    simpa [F, K, hD0, hC0, sub_mul] using hconst
  have hexp : Real.exp (-K t) * Real.exp (K t) = 1 := by
    rw [← Real.exp_add]; simp
  have hh := congrArg (fun x : ℝ => Real.exp (-K t)*x) he
  calc
    C t-r*D t = Real.exp (-K t)*(Real.exp (K t)*(C t-r*D t)) := by
      rw [← mul_assoc, hexp, one_mul]
    _ = Real.exp (-K t)*((1-r)*D0) := hh
    _ = (1-r)*D0*Real.exp (-(∫ s in (0:ℝ)..t, k s)) := by dsimp [K]; ring

theorem normalized_integrated_identity (D C q k : ℝ → ℝ) (r D0 t : ℝ)
    (hk : Continuous k) (hr : r < 1) (hpos : 0 < D0)
    (hD0 : D 0 = D0) (hC0 : C 0 = D0)
    (hD : ∀ s, HasDerivAt D (q s - k s * D s) s)
    (hC : ∀ s, HasDerivAt C (r*q s-k s*C s) s) :
    (C t-r*D t)/((1-r)*D0) = Real.exp (-(∫ s in (0:ℝ)..t, k s)) := by
  rw [paired_integrated_identity D C q k r D0 t hk hD0 hC0 hD hC]
  have hn : (1-r)*D0 ≠ 0 := ne_of_gt (mul_pos (sub_pos.mpr hr) hpos)
  exact mul_div_cancel_left₀ _ hn

/-- Variation of constants derived from the differential equation, rather than
assumed as an opaque observation premise. -/
theorem error_representation (Z k e : ℝ → ℝ) (t : ℝ)
    (hk : Continuous k) (he : Continuous e) (hZ0 : Z 0 = 1)
    (hZ : ∀ s, HasDerivAt Z (-k s * Z s + e s) s) :
    Z t - Real.exp (-(∫ s in (0:ℝ)..t, k s)) =
      ∫ s in (0:ℝ)..t,
        Real.exp ((∫ u in (0:ℝ)..s, k u) - (∫ u in (0:ℝ)..t, k u)) * e s := by
  let K : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, k s
  have hK (u : ℝ) : HasDerivAt K (k u) u :=
    intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _)
      hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hKcont : Continuous K := (show Differentiable ℝ K from
    fun u => (hK u).differentiableAt).continuous
  have hF (u : ℝ) : HasDerivAt (fun s => Real.exp (K s)*Z s)
      (Real.exp (K u)*e u) u := by
    convert (hK u).exp.mul (hZ u) using 1
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hF u) (((Real.continuous_exp.comp hKcont).mul he).intervalIntegrable 0 t)
  have hi : (∫ s in (0:ℝ)..t, Real.exp (K s)*e s) = Real.exp (K t)*Z t-1 := by
    simpa [K, hZ0] using hFTC
  have hexp : Real.exp (-K t)*Real.exp (K t)=1 := by
    rw [← Real.exp_add]; simp
  have hkernel : (∫ s in (0:ℝ)..t, Real.exp (K s-K t)*e s) =
      Real.exp (-K t)*(∫ s in (0:ℝ)..t, Real.exp (K s)*e s) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  change Z t-Real.exp (-K t) = ∫ s in (0:ℝ)..t, Real.exp (K s-K t)*e s
  rw [hkernel, hi, mul_sub, ← mul_assoc, hexp, one_mul, mul_one]

theorem integral_discrepancy_bound (Z k e : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hk : Continuous k) (he : Continuous e)
    (hkpos : ∀ s ∈ Set.Icc 0 t, 0 ≤ k s) (hZ0 : Z 0=1)
    (hZ : ∀ s, HasDerivAt Z (-k s*Z s+e s) s) :
    |Z t-Real.exp (-(∫ s in (0:ℝ)..t, k s))| ≤ ∫ s in (0:ℝ)..t, |e s| := by
  rw [error_representation Z k e t hk he hZ0 hZ]
  let K : ℝ → ℝ := fun u => ∫ s in (0:ℝ)..u, k s
  have hKcont : Continuous K :=
    (intervalIntegral.differentiable_integral_of_continuous hk).continuous
  have hc : Continuous (fun s => Real.exp (K s-K t)*e s) :=
    (Real.continuous_exp.comp (hKcont.sub continuous_const)).mul he
  apply (intervalIntegral.abs_integral_le_integral_abs ht).trans
  apply intervalIntegral.integral_mono_on ht (hc.abs.intervalIntegrable _ _)
    (he.abs.intervalIntegrable _ _)
  intro s hs
  have hn : 0 ≤ ∫ u in s..t, k u :=
    intervalIntegral.integral_nonneg hs.2 (fun u hu => hkpos u ⟨hs.1.trans hu.1,hu.2⟩)
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hk.intervalIntegrable 0 s) (hk.intervalIntegrable s t)
  have hle : K s-K t ≤ 0 := by dsimp [K]; linarith
  have hexple : Real.exp (K s-K t) ≤ 1 := Real.exp_le_one_iff.mpr hle
  change |Real.exp (K s-K t)*e s| ≤ |e s|
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa using mul_le_mul_of_nonneg_right hexple (abs_nonneg (e s))

/-- The discrepancy bound instantiated with the actual paired equations.
The normalization and treatment-error mapping are proved explicitly. -/
theorem paired_robustness (D C q k eta delta : ℝ → ℝ) (r D0 t : ℝ)
    (ht : 0 ≤ t) (hr : r < 1) (hpos : 0 < D0)
    (hk : Continuous k) (heta : Continuous eta) (hdelta : Continuous delta)
    (hkpos : ∀ s ∈ Set.Icc 0 t, 0 ≤ k s)
    (hD0 : D 0=D0) (hC0 : C 0=D0)
    (hD : ∀ s, HasDerivAt D (q s-k s*D s) s)
    (hC : ∀ s, HasDerivAt C (r*q s+eta s-(k s+delta s)*C s) s) :
    |(C t-r*D t)/((1-r)*D0)-Real.exp (-(∫ s in (0:ℝ)..t,k s))| ≤
      ∫ s in (0:ℝ)..t, |(eta s-delta s*C s)/((1-r)*D0)| := by
  let n := (1-r)*D0
  have hn : n ≠ 0 := ne_of_gt (mul_pos (sub_pos.mpr hr) hpos)
  let Z : ℝ → ℝ := fun s => (C s-r*D s)/n
  let e : ℝ → ℝ := fun s => (eta s-delta s*C s)/n
  have hCc : Continuous C := (show Differentiable ℝ C from
    fun s => (hC s).differentiableAt).continuous
  have he : Continuous e := (heta.sub (hdelta.mul hCc)).div_const n
  have hZ0 : Z 0=1 := by
    dsimp [Z]
    rw [hC0,hD0]
    have hnum : D0-r*D0=n := by dsimp [n]; ring
    rw [hnum, div_self hn]
  have hZ (s : ℝ) : HasDerivAt Z (-k s*Z s+e s) s := by
    convert (paired_discrepancy D C q k eta delta r s (hD s) (hC s)).div_const n using 1
    dsimp [Z,e]
    field_simp
    ring
  exact integral_discrepancy_bound Z k e t ht hk he hkpos hZ0 hZ

/-- Sensor and intervention errors combine additively before taking logs. -/
theorem observation_rate_interval (Z E K zhat Gamma eps : ℝ)
    (hE : E=Real.exp (-K)) (hK : 0 ≤ K)
    (hd : |Z-E| ≤ Gamma) (ho : |zhat-Z| ≤ eps)
    (hL : 0 < zhat-(Gamma+eps)) :
    -Real.log (min 1 (zhat+(Gamma+eps))) ≤ K ∧
      K ≤ -Real.log (zhat-(Gamma+eps)) := by
  have hb : |zhat-E| ≤ Gamma+eps := by
    calc
      |zhat-E| = |(zhat-Z)+(Z-E)| := by congr 1; ring
      _ ≤ |zhat-Z|+|Z-E| := abs_add_le _ _
      _ ≤ Gamma+eps := by linarith
  have hh := abs_le.mp hb
  have hEp : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hEone : E ≤ 1 := by rw [hE]; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  have hEL : zhat-(Gamma+eps) ≤ E := by linarith
  have hEU : E ≤ min 1 (zhat+(Gamma+eps)) := le_min hEone (by linarith)
  have hlo := Real.log_le_log hL hEL
  have hhi := Real.log_le_log hEp hEU
  rw [hE, Real.log_exp] at hlo hhi
  constructor <;> linarith

end
end StoredRedCells.PairedRecovery

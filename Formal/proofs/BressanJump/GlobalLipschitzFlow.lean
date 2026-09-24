import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.Transform
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime

/-!
# Complete flows for bounded globally Lipschitz autonomous fields

This module supplies the missing complete-flow producer used by the finite
primitive-shear Lie approximation.  The first layer is a small Euclidean
globalization theorem: a uniform local existence interval can be extended to
a global integral curve.
-/

noncomputable section

open Set
open Bundle

open scoped Manifold NNReal Topology

namespace BressanJump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contMDiff_tangentSection_self
    {f : E → E} (hf : ContDiff ℝ 1 f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x : E => (⟨x, f x⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  have hidM : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun x : E => x) :=
    contDiff_id.contMDiff
  have hfM : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f := hf.contMDiff
  have hpair : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 1
      (fun x : E => (x, f x)) := hidM.prodMk hfM
  rw [chartedSpaceSelf_prod] at hpair
  let e := tangentBundleModelSpaceDiffeomorph (I := 𝓘(ℝ, E)) (1 : ℕ∞)
  apply (e.contMDiff_diffeomorph_comp_iff (m := (1 : ℕ∞))
    (f := fun x : E => (⟨x, f x⟩ : TangentBundle 𝓘(ℝ, E) E)) le_rfl).mp
  change ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 1
    (fun x : E => (show ModelProd E E from (x, f x)))
  simpa only [ModelProd] using hpair

theorem exists_global_isIntegralCurve_of_uniform_local
    [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f)
    {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-ε) ε, HasDerivAt γ (f (γ t)) t)
    (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ => f) := by
  letI : ContinuousSMul ℝ E := IsBoundedSMul.continuousSMul
  have hlocalM : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, E)) γ f (Ioo (-ε) ε) := by
    intro y
    obtain ⟨γ, hγ0, hγ⟩ := hlocal y
    refine ⟨γ, hγ0, ?_⟩
    intro t ht
    exact (hγ t ht).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨γ, hγ0, hγ⟩ :=
    exists_isMIntegralCurve_of_isMIntegralCurveOn (I := 𝓘(ℝ, E))
      (contMDiff_tangentSection_self hf) hε hlocalM x
  refine ⟨γ, hγ0, fun t => ?_⟩
  rw [hasDerivAt_iff_hasFDerivAt]
  exact (hγ t).hasFDerivAt

/-- A bounded globally Lipschitz `C¹` autonomous vector field on a complete
normed space has a global integral curve through every point. -/
theorem exists_global_isIntegralCurve_of_bounded_lipschitz
    [CompleteSpace E]
    {f : E → E} (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ IsIntegralCurve γ (fun _ => f) := by
  let ε : ℝ := 1 / ((B : ℝ) + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  apply exists_global_isIntegralCurve_of_uniform_local hf hε
  intro y
  have hzero : (0 : ℝ) ∈ Icc (-ε) ε := by
    simp only [mem_Icc]
    exact ⟨neg_nonpos.mpr hε.le, hε.le⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => f)
      (tmin := -ε) (tmax := ε) ⟨0, hzero⟩ y 1 0 B K := by
    apply IsPicardLindelof.of_time_independent
    · intro z _hz
      exact hbound z
    · exact hlip.lipschitzOnWith
    · change (B : ℝ) * max (ε - 0) (0 - -ε) ≤ (1 : ℝ) - 0
      rw [sub_zero, zero_sub, neg_neg, max_self, sub_zero]
      dsimp [ε]
      rw [one_div, ← div_eq_mul_inv, div_le_one]
      · linarith [B.coe_nonneg]
      · positivity
  obtain ⟨γ, hγ0, hγ⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, fun t ht => ?_⟩
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- A canonical choice of the complete trajectory through every initial
point. Uniqueness below makes all observable properties independent of this
choice. -/
noncomputable def globalLipschitzFlow
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f) :
    ℝ → E → E := fun t x =>
  Classical.choose
    (exists_global_isIntegralCurve_of_bounded_lipschitz hf B K hbound hlip x) t

theorem globalLipschitzFlow_zero
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (x : E) :
    globalLipschitzFlow f hf B K hbound hlip 0 x = x := by
  exact (Classical.choose_spec
    (exists_global_isIntegralCurve_of_bounded_lipschitz
      hf B K hbound hlip x)).1

theorem globalLipschitzFlow_isIntegralCurve
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (x : E) :
    IsIntegralCurve
      (fun t => globalLipschitzFlow f hf B K hbound hlip t x)
      (fun _ => f) := by
  exact (Classical.choose_spec
    (exists_global_isIntegralCurve_of_bounded_lipschitz
      hf B K hbound hlip x)).2

theorem globalLipschitzFlow_add
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (s t : ℝ) (x : E) :
    globalLipschitzFlow f hf B K hbound hlip s
        (globalLipschitzFlow f hf B K hbound hlip t x) =
      globalLipschitzFlow f hf B K hbound hlip (t + s) x := by
  let Φ := globalLipschitzFlow f hf B K hbound hlip
  have hcurve (y : E) : IsIntegralCurve (fun r => Φ r y) (fun _ => f) :=
    globalLipschitzFlow_isIntegralCurve f hf B K hbound hlip y
  have hshift : IsIntegralCurve (fun r => Φ (r + t) x) (fun _ => f) := by
    simpa only [Function.comp_apply] using (hcurve x).comp_add t
  have heq : (fun r => Φ r (Φ t x)) = (fun r => Φ (r + t) x) := by
    apply ODE_solution_unique_univ
      (v := fun _ => f) (s := fun _ => univ) (K := K) (t₀ := 0)
    · intro _
      exact hlip.lipschitzOnWith
    · intro r
      exact ⟨hcurve (Φ t x) r, mem_univ _⟩
    · intro r
      exact ⟨hshift r, mem_univ _⟩
    · simp only [zero_add]
      exact globalLipschitzFlow_zero f hf B K hbound hlip (Φ t x) |>.trans rfl
  simpa only [Φ, add_comm] using congrFun heq s

private theorem autonomousODE_exp_stable_global
    (f g : ℝ → E) (G : E → E) (h K : ℝ)
    (hh : 0 ≤ h) (hK : 0 ≤ K) (hG : LipschitzWith ⟨K, hK⟩ G)
    (hfODE : ∀ t, HasDerivAt f (G (f t)) t)
    (hgODE : ∀ t, HasDerivAt g (G (g t)) t) :
    dist (f h) (g h) ≤ Real.exp (K * h) * dist (f 0) (g 0) := by
  have hfcont : Continuous f := continuous_iff_continuousAt.2
    (fun t => (hfODE t).continuousAt)
  have hgcont : Continuous g := continuous_iff_continuousAt.2
    (fun t => (hgODE t).continuousAt)
  have hgr := dist_le_of_trajectories_ODE
    (v := fun _t => G) (K := ⟨K, hK⟩)
    (f := f) (g := g) (a := (0 : ℝ)) (b := h)
    (δ := dist (f 0) (g 0))
    (fun _ => hG)
    hfcont.continuousOn
    (fun t _ht => (hfODE t).hasDerivWithinAt)
    hgcont.continuousOn
    (fun t _ht => (hgODE t).hasDerivWithinAt)
    le_rfl h ⟨hh, le_rfl⟩
  simpa only [sub_zero, NNReal.smul_def, NNReal.coe_mk, mul_comm] using hgr

theorem globalLipschitzFlow_dist_le
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (t : ℝ) (x y : E) :
    dist (globalLipschitzFlow f hf B K hbound hlip t x)
        (globalLipschitzFlow f hf B K hbound hlip t y) ≤
      Real.exp ((K : ℝ) * |t|) * dist x y := by
  let Φ := globalLipschitzFlow f hf B K hbound hlip
  have hcurve (z : E) : IsIntegralCurve (fun r => Φ r z) (fun _ => f) :=
    globalLipschitzFlow_isIntegralCurve f hf B K hbound hlip z
  by_cases ht : 0 ≤ t
  · simpa only [Φ, abs_of_nonneg ht,
      globalLipschitzFlow_zero f hf B K hbound hlip] using
      autonomousODE_exp_stable_global
        (fun r => Φ r x) (fun r => Φ r y) f t (K : ℝ) ht K.coe_nonneg
        hlip (hcurve x) (hcurve y)
  · have hneg : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    have hrev (z : E) : IsIntegralCurve (fun r => Φ (-r) z) (fun _r w => -f w) := by
      intro r
      have hr : HasDerivAt (fun q : ℝ => -q) (-1) r := hasDerivAt_neg r
      simpa only [one_smul, neg_smul] using
        (hcurve z (-r)).scomp r hr
    have hest := autonomousODE_exp_stable_global
      (fun r => Φ (-r) x) (fun r => Φ (-r) y) (fun z => -f z)
      (-t) (K : ℝ) hneg K.coe_nonneg hlip.neg (hrev x) (hrev y)
    simpa only [neg_neg, neg_zero, Φ,
      globalLipschitzFlow_zero f hf B K hbound hlip,
      abs_of_nonpos (le_of_not_ge ht)] using hest

theorem globalLipschitzFlow_lipschitz
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (t : ℝ) :
    LipschitzWith ⟨Real.exp ((K : ℝ) * |t|), Real.exp_pos _ |>.le⟩
      (globalLipschitzFlow f hf B K hbound hlip t) :=
  LipschitzWith.of_dist_le_mul fun x y =>
    globalLipschitzFlow_dist_le f hf B K hbound hlip t x y

/-- Every time slice of the canonical complete flow is a homeomorphism; its
inverse is the time `-t` slice. -/
noncomputable def globalLipschitzFlowHomeomorph
    [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f)
    (B K : ℝ≥0)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlip : LipschitzWith K f)
    (t : ℝ) : E ≃ₜ E where
  toFun := globalLipschitzFlow f hf B K hbound hlip t
  invFun := globalLipschitzFlow f hf B K hbound hlip (-t)
  left_inv x := by
    rw [globalLipschitzFlow_add]
    simp only [add_neg_cancel]
    exact globalLipschitzFlow_zero f hf B K hbound hlip x
  right_inv x := by
    rw [globalLipschitzFlow_add]
    simp only [neg_add_cancel]
    exact globalLipschitzFlow_zero f hf B K hbound hlip x
  continuous_toFun :=
    (globalLipschitzFlow_lipschitz f hf B K hbound hlip t).continuous
  continuous_invFun :=
    (globalLipschitzFlow_lipschitz f hf B K hbound hlip (-t)).continuous

end BressanJump

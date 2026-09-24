import proofs.OscillatoryCores.SpectralTransversality
import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace OscillatoryCores

open Filter
open scoped ContDiff Topology

noncomputable def universalQuartic (p : ℂ × ℂ) : ℂ :=
  p.2^4 + (386/125+201*p.1)*p.2^3 + ((562+5297*p.1)/250)*p.2^2 +
    ((40+479*p.1)/250)*p.2 + 6*p.1/25

theorem universalQuartic_real (t : ℝ) (z : ℂ) :
    universalQuartic ((t : ℂ),z) = quarticC t z := by
  unfold universalQuartic quarticC a1 a2 a3 a4
  push_cast
  ring

theorem universalQuartic_left_hasDerivAt (s z : ℂ) :
    HasDerivAt (fun x : ℂ => universalQuartic (x,z)) (quarticParameterDerivativeC z) s := by
  have he : (fun x : ℂ => universalQuartic (x,z)) =
      (fun x : ℂ => universalQuartic (0,z)+x*quarticParameterDerivativeC z) := by
    funext x
    unfold universalQuartic quarticParameterDerivativeC
    ring
  rw [he]
  simpa using ((hasDerivAt_id s).mul_const (quarticParameterDerivativeC z)).const_add
    (universalQuartic (0,z))

/-- A genuine smooth branch of the simple characteristic root. -/
theorem eigenvalue_branch_exists {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    ∃ ψ : ℂ → ℂ,
      ψ (t : ℂ) = Complex.I*(spectralFrequency t : ℂ) ∧
      ContDiffAt ℂ ∞ ψ (t : ℂ) ∧
      (∀ᶠ s in 𝓝 (t : ℂ), universalQuartic (s,ψ s)=0) ∧
      HasDerivAt ψ
        (-quarticParameterDerivativeC (Complex.I*(spectralFrequency t : ℂ)) /
          quarticDerivativeC t (Complex.I*(spectralFrequency t : ℂ))) (t : ℂ) := by
  let z : ℂ := Complex.I*(spectralFrequency t : ℂ)
  let D := fderiv ℂ universalQuartic ((t : ℂ),z)
  have hc : ContDiffAt ℂ ∞ universalQuartic ((t : ℂ),z) := by
    have h : ContDiff ℂ ∞ universalQuartic := by unfold universalQuartic; fun_prop
    exact h.contDiffAt
  have hF : HasFDerivAt universalQuartic D ((t : ℂ),z) :=
    (hc.differentiableAt (by simp)).hasFDerivAt
  have hri : HasFDerivAt (fun x : ℂ => ((t : ℂ),x)) (ContinuousLinearMap.inr ℂ ℂ ℂ) z := by
    simpa using (hasFDerivAt_const (t : ℂ) z).prodMk (hasFDerivAt_id z)
  have hli : HasFDerivAt (fun x : ℂ => (x,z)) (ContinuousLinearMap.inl ℂ ℂ ℂ) (t : ℂ) := by
    simpa using (hasFDerivAt_id (t : ℂ)).prodMk (hasFDerivAt_const z (t : ℂ))
  have hR : D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ (quarticDerivativeC t z) := by
    have h : HasFDerivAt (quarticC t) (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) z := by
      simpa only [Function.comp_def,universalQuartic_real] using hF.comp z hri
    exact h.unique (quartic_hasDerivAt t z).hasFDerivAt
  have hL : D ∘L ContinuousLinearMap.inl ℂ ℂ ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ (quarticParameterDerivativeC z) := by
    have h : HasFDerivAt (fun x : ℂ => universalQuartic (x,z))
        (D ∘L ContinuousLinearMap.inl ℂ ℂ ℂ) (t : ℂ) := by
      simpa only [Function.comp_def] using hF.comp (t : ℂ) hli
    exact h.unique (universalQuartic_left_hasDerivAt (t : ℂ) z).hasFDerivAt
  let Rinv := ContinuousLinearMap.toSpanSingleton ℂ (quarticDerivativeC t z)⁻¹
  have hne : quarticDerivativeC t z ≠ 0 := imaginary_root_simple ht
  have hright : (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) ∘L Rinv = ContinuousLinearMap.id ℂ ℂ := by
    rw [hR]
    ext
    simp [Rinv,hne]
  have hleft : Rinv ∘L (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ) = ContinuousLinearMap.id ℂ ℂ := by
    rw [hR]
    ext
    simp [Rinv,hne]
  have hinv : (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hright hleft
  have hinveq : (D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).inverse = Rinv :=
    ContinuousLinearMap.inverse_eq hright hleft
  let ψ := hc.implicitFunction (by simp) hinv
  refine ⟨ψ,hc.implicitFunction_apply_self (by simp) hinv,
    hc.contDiffAt_implicitFunction (by simp) hinv,?_,?_⟩
  · have he := hc.eventually_apply_implicitFunction (by simp) hinv
    simpa only [universalQuartic_real,z,imaginary_quartic_root ht hz] using he
  · have he := (hc.hasStrictFDerivAt_implicitFunction (by simp) hinv).hasFDerivAt.hasDerivAt
    change HasDerivAt ψ ((-(D ∘L ContinuousLinearMap.inr ℂ ℂ ℂ).inverse ∘L
      (D ∘L ContinuousLinearMap.inl ℂ ℂ ℂ)) 1) (t : ℂ) at he
    rw [hinveq,hL] at he
    simpa [Rinv,div_eq_mul_inv,mul_comm] using he

end OscillatoryCores

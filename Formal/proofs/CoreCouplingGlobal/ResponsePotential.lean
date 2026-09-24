import proofs.CoreCouplingGlobal.Response
import proofs.CoreCouplingGlobal.HResponse
import proofs.CoreCouplingGlobal.ResponseEnergy

namespace CoreCouplingGlobal
open Set

/-- Clamping a continuous integrand gives a genuine global primitive on a closed interval. -/
theorem primitive_on_Icc (f : ℝ → ℝ) (l u : ℝ) (hlu : l ≤ u)
    (hf : ContinuousOn f (Icc l u)) :
    ∃ P : ℝ → ℝ, Continuous P ∧ ∀ x ∈ Icc l u, HasDerivAt P (f x) x := by
  let k : ℝ → ℝ := fun x => max l (min u x)
  have hk : Continuous k := continuous_const.max (continuous_const.min continuous_id)
  have hkm : ∀ x, k x ∈ Icc l u := by
    intro x
    exact ⟨le_max_left _ _,max_le hlu (min_le_left _ _)⟩
  have hfk : Continuous (fun x => f (k x)) := hf.comp_continuous hk hkm
  refine ⟨fun x => ∫ t in l..x, f (k t),?_,?_⟩
  · exact continuous_iff_continuousAt.2 fun x =>
      (hfk.integral_hasStrictDerivAt l x).hasDerivAt.continuousAt
  · intro x hx
    have hxx : k x = x := by dsimp [k]; rw [min_eq_right hx.2,max_eq_right hx.1]
    simpa only [hxx] using (hfk.integral_hasStrictDerivAt l x).hasDerivAt

noncomputable def responsePIntegrand (e B : ℝ) : ℝ :=
  -Real.log (60/B)+responseSlope e B*responseLog (60/B-2)

theorem responseA_continuous (e : ℝ) : Continuous (responseA e) := by
  unfold responseA
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  positivity

theorem responsePIntegrand_continuousOn (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000) :
    ContinuousOn (responsePIntegrand e) (Icc 2 34) := by
  intro B hB
  have hB0 : B ≠ 0 := by linarith [hB.1]
  have hbpos : 0 < 60/B := div_pos (by norm_num) (by linarith [hB.1])
  have hb1 : -1 < 60/B-2 := by
    have hratio : 1 < 60/B := (lt_div_iff₀ (by linarith [hB.1])).2 (by linarith [hB.2])
    linarith
  have hrat : ContinuousAt (fun x : ℝ => 60/x) B := continuousAt_const.div continuousAt_id hB0
  obtain ⟨hl,_⟩ := response_bounds e B he he' hB.1 hB.2
  have hmul := mul_le_mul_of_nonneg_left hl he
  have hden : 1+2*e*responseA e B ≠ 0 := by nlinarith
  have hc : ContinuousAt (responseSlope e) B := by
    unfold responseSlope
    exact (continuousAt_const.mul (continuousAt_const.add
      (continuousAt_const.mul (responseA_continuous e).continuousAt))).div
      (continuousAt_const.add (continuousAt_const.mul (responseA_continuous e).continuousAt)) hden
  exact ((hrat.log (ne_of_gt hbpos)).neg.add
    (hc.mul ((responseLog_hasDerivAt _ hb1).continuousAt.comp
      (f := fun x : ℝ => 60/x-2) (hrat.sub continuousAt_const)))).continuousWithinAt

structure PotentialPrimitives (e : ℝ) where
  U : ℝ → ℝ
  P : ℝ → ℝ
  R : ℝ → ℝ
  continuousU : Continuous U
  continuousP : Continuous P
  continuousR : Continuous R
  derivU : ∀ z ∈ Icc (0:ℝ) 12, HasDerivAt U ((16*z+4*z^2)/((z+1)*(z+2))) z
  derivP : ∀ B ∈ Icc (2:ℝ) 34, HasDerivAt P (responsePIntegrand e B) B
  derivR : ∀ H ∈ Icc (0:ℝ) (1536/7), HasDerivAt R (3*responseLog (responsePhi H)) H

theorem potentialPrimitives_nonempty (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000) :
    Nonempty (PotentialPrimitives e) := by
  have hU : ContinuousOn (fun z : ℝ => (16*z+4*z^2)/((z+1)*(z+2))) (Icc 0 12) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro z hz
    have hz0 := hz.1
    positivity
  have hphi : Continuous responsePhi := by
    unfold responsePhi
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  have hR : ContinuousOn (fun H => 3*responseLog (responsePhi H)) (Icc (0:ℝ) (1536/7)) := by
    intro H hH
    have hp := (responsePhi_bounds H hH.1 hH.2).1
    exact (continuousAt_const.mul ((responseLog_hasDerivAt _ (by linarith)).continuousAt.comp (f := responsePhi)
      hphi.continuousAt)).continuousWithinAt
  obtain ⟨U,hUc,hUd⟩ := primitive_on_Icc _ 0 12 (by norm_num) hU
  obtain ⟨P,hPc,hPd⟩ := primitive_on_Icc _ 2 34 (by norm_num)
    (responsePIntegrand_continuousOn e he he')
  obtain ⟨R,hRc,hRd⟩ := primitive_on_Icc _ 0 (1536/7) (by norm_num) hR
  exact ⟨⟨U,P,R,hUc,hPc,hRc,hUd,hPd,hRd⟩⟩

noncomputable def responsePotential (e : ℝ) (p : PotentialPrimitives e)
    (B z H r : ℝ) : ℝ :=
  B*Real.log (z+2)-responseTotal e B*responseLog z+p.U z-3*H*responseLog z+
    p.P B+p.R H+r^2/2

end CoreCouplingGlobal

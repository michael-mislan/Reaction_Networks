import proofs.CommonEnvironmentProtection.MonotoneResponse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace CommonEnvironmentProtection.MaintainedSource
noncomputable section

/-! Source scope: Adimora 2010 Table 1 R20, R21, R22 under maintained
partner concentrations. x is NADPH, P-x is NADP+, N=P-NADP_initial,
D=K7+P, cG=k20*(GSSG-GSSG_initial), cT=k21*(Trxox-Trxox_initial).
All quantities use a consistent concentration/time convention. -/

def supply (s V N D x : ℝ) : ℝ := s * V * (N-x) / (D-x)
def drift (s V N D c m x : ℝ) : ℝ := supply s V N D x - c*x - m

theorem drift_strictAnti (s V N D c m : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hND : N < D) (hc : 0 ≤ c) :
    StrictAntiOn (drift s V N D c m) (Set.Iic N) := by
  intro x hx y hy hxy
  have hdx : 0 < D-x := by have := hx; change x ≤ N at this; linarith
  have hdy : 0 < D-y := by have := hy; change y ≤ N at this; linarith
  have hr : (N-y)/(D-y) < (N-x)/(D-x) := by
    rw [div_lt_div_iff₀ hdy hdx]
    nlinarith [mul_pos (sub_pos.mpr hND) (sub_pos.mpr hxy)]
  have hmul := mul_lt_mul_of_pos_left hr (mul_pos hs hV)
  have hlin := mul_le_mul_of_nonneg_left hxy.le hc
  unfold drift supply
  simp only [← mul_div_assoc] at *
  linarith

theorem drift_continuous (s V N D c m L U : ℝ)
    (hND : N < D) (hUN : U ≤ N) :
    ContinuousOn (drift s V N D c m) (Set.Icc L U) := by
  have hn : ContinuousOn (fun x : ℝ => s*V*(N-x)) (Set.Icc L U) := by
    exact continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
  have hd : ContinuousOn (fun x : ℝ => D-x) (Set.Icc L U) :=
    continuousOn_const.sub continuousOn_id
  have hz : ∀ x ∈ Set.Icc L U, D-x ≠ 0 := by
    intro x hx
    have : x ≤ U := hx.2
    linarith
  exact ((hn.div hd hz).sub (continuousOn_const.mul continuousOn_id)).sub
    continuousOn_const

theorem endpoint_criterion (s V N D c m L U : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hND : N < D) (hc : 0 ≤ c)
    (hLU : L ≤ U) (hUN : U ≤ N) :
    (∃! x, x ∈ Set.Icc L U ∧ drift s V N D c m x = 0) ↔
      0 ≤ drift s V N D c m L ∧ drift s V N D c m U ≤ 0 := by
  apply CommonEnvironmentProtection.safe_equilibrium_iff _ _ _ hLU
    (drift_continuous s V N D c m L U hND hUN)
  exact (drift_strictAnti s V N D c m hs hV hND hc).mono
    (fun _ hx => hx.2.trans hUN)

def repairScale (V N D c m L : ℝ) : ℝ := (c*L+m)*(D-L)/(V*(N-L))

theorem lower_sign_iff (s V N D c m L : ℝ)
    (hV : 0 < V) (hLN : L < N) (hND : N < D) :
    0 ≤ drift s V N D c m L ↔ repairScale V N D c m L ≤ s := by
  have hd : 0 < D-L := by linarith
  have hv : 0 < V*(N-L) := mul_pos hV (sub_pos.mpr hLN)
  unfold drift repairScale
  have heq : supply s V N D L = s*(V*(N-L))/(D-L) := by
    unfold supply
    ring
  rw [heq, div_le_iff₀ hv]
  have hdiv := le_div_iff₀ (a := c*L+m) (b := s*(V*(N-L))) hd
  constructor
  · intro h
    have hh : c*L+m ≤ s*(V*(N-L))/(D-L) := by linarith
    exact hdiv.mp hh
  · intro h
    have hh : c*L+m ≤ s*(V*(N-L))/(D-L) :=
      hdiv.mpr h
    linarith

/-- Exact scale boundary, including unique attainable equilibrium. -/
theorem repair_iff (s V N D c m L : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hN : 0 ≤ N) (hND : N < D)
    (hc : 0 ≤ c) (hm : 0 ≤ m) (hLN : L < N) :
    (∃! x, x ∈ Set.Icc L N ∧ drift s V N D c m x = 0) ↔
      repairScale V N D c m L ≤ s := by
  rw [endpoint_criterion s V N D c m L N hs hV hND hc hLN.le le_rfl,
    lower_sign_iff s V N D c m L hV hLN hND]
  have hu : drift s V N D c m N ≤ 0 := by
    unfold drift supply
    simp only [sub_self, mul_zero, zero_div, zero_sub]
    nlinarith [mul_nonneg hc hN]
  exact and_iff_left hu

def Joint (s V N D cG cT qG qT : ℝ) : Prop :=
  ∃ x : ℝ, 0 ≤ x ∧ x ≤ N ∧
    supply s V N D x = cG*x+cT*x ∧ qG ≤ cG*x ∧ qT ≤ cT*x

/-- Source-derived joint service criterion for the maintained reductase assay.
This reconstructs one shared NADPH state, not independent branch states. -/
theorem joint_iff_repair (s V N D cG cT qG qT : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hND : N < D)
    (hcG : 0 < cG) (hcT : 0 < cT) (hqG : 0 < qG)
    (hLN : max (qG/cG) (qT/cT) < N) :
    Joint s V N D cG cT qG qT ↔
      repairScale V N D (cG+cT) 0 (max (qG/cG) (qT/cT)) ≤ s := by
  let L := max (qG/cG) (qT/cT)
  have hL : 0 < L := lt_of_lt_of_le (div_pos hqG hcG) (le_max_left _ _)
  have hN : 0 ≤ N := (hL.trans hLN).le
  have hc : 0 ≤ cG+cT := (add_pos hcG hcT).le
  have uniq := drift_strictAnti s V N D (cG+cT) 0 hs hV hND hc
  rw [← repair_iff s V N D (cG+cT) 0 L hs hV hN hND hc (le_refl 0) hLN]
  constructor
  · rintro ⟨x, _, hxN, hb, hg, ht⟩
    have hxL : L ≤ x := max_le ((div_le_iff₀ hcG).mpr (by nlinarith))
      ((div_le_iff₀ hcT).mpr (by nlinarith))
    have hz : drift s V N D (cG+cT) 0 x = 0 := by unfold drift; nlinarith
    refine ⟨x, ⟨⟨hxL,hxN⟩,hz⟩, ?_⟩
    intro y hy
    exact uniq.injOn hy.1.2 hxN (hy.2.trans hz.symm)
  · rintro ⟨x, ⟨hx,hz⟩, _⟩
    have hgl : qG/cG ≤ x := (le_max_left _ _).trans hx.1
    have htl : qT/cT ≤ x := (le_max_right _ _).trans hx.1
    refine ⟨x, hL.le.trans hx.1, hx.2, ?_, ?_, ?_⟩
    · unfold drift at hz
      nlinarith
    · have := (div_le_iff₀ hcG).mp hgl
      nlinarith
    · have := (div_le_iff₀ hcT).mp htl
      nlinarith

def LiteralJoint (s V K P P₀ kG oG g₀ kT oT t₀ qG qT : ℝ) : Prop :=
  ∃ x p : ℝ, 0 ≤ x ∧ P₀ ≤ p ∧ x+p=P ∧
    s*V*(p-P₀)/(K+p) = kG*(oG-g₀)*x+kT*(oT-t₀)*x ∧
    qG ≤ kG*(oG-g₀)*x ∧ qT ≤ kT*(oT-t₀)*x

theorem source_supply_identity (s V K P P₀ x : ℝ) :
    supply s V (P-P₀) (K+P) x = s*V*((P-x)-P₀)/(K+(P-x)) := by
  unfold supply
  congr 1 <;> ring

theorem literal_joint_iff_joint (s V K P P₀ kG oG g₀ kT oT t₀ qG qT : ℝ) :
    LiteralJoint s V K P P₀ kG oG g₀ kT oT t₀ qG qT ↔
      Joint s V (P-P₀) (K+P) (kG*(oG-g₀)) (kT*(oT-t₀)) qG qT := by
  constructor
  · rintro ⟨x,p,hx,hp,hpool,hb,hg,ht⟩
    have he : p = P-x := by linarith
    subst p
    refine ⟨x,hx,by linarith,?_,hg,ht⟩
    rwa [source_supply_identity]
  · rintro ⟨x,hx,hxN,hb,hg,ht⟩
    refine ⟨x,P-x,hx,by linarith,by ring,?_,hg,ht⟩
    rwa [source_supply_identity] at hb

/-- The literal source laws, one pool identity, and both service quotas are
equivalent to the explicit regeneration multiplier inequality. -/
theorem literal_joint_iff_repair
    (s V K P P₀ kG oG g₀ kT oT t₀ qG qT : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hK : 0 < K) (hP₀ : 0 ≤ P₀)
    (hkG : 0 < kG) (hoG : g₀ < oG) (hkT : 0 < kT) (hoT : t₀ < oT)
    (hqG : 0 < qG)
    (hL : max (qG/(kG*(oG-g₀))) (qT/(kT*(oT-t₀))) < P-P₀) :
    LiteralJoint s V K P P₀ kG oG g₀ kT oT t₀ qG qT ↔
      repairScale V (P-P₀) (K+P) (kG*(oG-g₀)+kT*(oT-t₀)) 0
        (max (qG/(kG*(oG-g₀))) (qT/(kT*(oT-t₀)))) ≤ s := by
  rw [literal_joint_iff_joint]
  exact joint_iff_repair _ _ _ _ _ _ _ _ hs hV (by linarith)
    (mul_pos hkG (sub_pos.mpr hoG)) (mul_pos hkT (sub_pos.mpr hoT)) hqG hL

end
end CommonEnvironmentProtection.MaintainedSource

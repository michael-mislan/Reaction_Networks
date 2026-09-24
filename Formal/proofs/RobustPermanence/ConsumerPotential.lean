import proofs.RobustPermanence.ConsumerAbsorber
import proofs.RobustPermanence.ConsumerDissipation
import proofs.RobustPermanence.LogCorrector

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC Filter Topology Set

noncomputable def trajectoryPotential (e : ℝ) (p : PotentialPrimitives e)
    (S : ℝ → State) (t : ℝ) : ℝ :=
  responsePotential e p (S t).B (S t).z (S t).H
    ((S t).A+(S t).B-responseTotal e (S t).B)

theorem consumer_potential_hasDerivAt (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (S : ℝ → State) (x : ℝ → ℝ) (hS : IsConsumerTrajectory e S x)
    (t : ℝ) (ht : 0 ≤ t) (hB : (S t).B ∈ Icc (2:ℝ) 34)
    (hz : (S t).z ∈ Icc (0:ℝ) 12) (hH : (S t).H ∈ Icc (0:ℝ) (1536/7)) :
    HasDerivAt (trajectoryPotential e p S)
      (potentialRate e (S t).A (S t).B (S t).z (S t).H (x t)) t := by
  have dr := ((hS.dA t ht).add (hS.dB t ht)).sub
    ((responseTotal_hasDerivAt e (S t).B he he' hB.1 hB.2).comp t (hS.dB t ht))
  have hh := responsePotential_hasDerivAt e p he he'
    (fun t => (S t).B) (fun t => (S t).z) (fun t => (S t).H)
    (fun t => (S t).A+(S t).B-responseTotal e (S t).B) t _ _ _ _
    hB hz hH (hS.dB t ht) (hS.dz t ht) (hS.dH t ht) dr
  exact hh

/-- Compactness gives finite potential bounds on the literal resident box.
These bounds depend on e and the selected primitives; no trajectory enters the quantifiers. -/
theorem potential_box_bounds (e : ℝ) (p : PotentialPrimitives e) :
    ∃ L U : ℝ, ∀ A B z H : ℝ,
      0 ≤ A → A ≤ 34 → 2 ≤ B → B ≤ 34 → 0 ≤ z → z ≤ 12 →
      0 ≤ H → H ≤ 1536/7 →
      L ≤ responsePotential e p B z H (A+B-responseTotal e B) ∧
      responsePotential e p B z H (A+B-responseTotal e B) ≤ U := by
  let V : (Fin 4 → ℝ) → ℝ := fun q => responsePotential e p (q 1) (max 0 (q 2))
    (q 3) (q 0+q 1-responseTotal e (q 1))
  have hcoord (i : Fin 4) : Continuous (fun q : Fin 4 → ℝ => q i) := continuous_apply i
  have hz : Continuous (fun q : Fin 4 → ℝ => max 0 (q 2)) := continuous_const.max (hcoord 2)
  have hlog1 : Continuous (fun q : Fin 4 → ℝ => Real.log (max 0 (q 2)+1)) :=
    (hz.add_const 1).log (fun q => ne_of_gt (by positivity))
  have hlog2 : Continuous (fun q : Fin 4 → ℝ => Real.log (max 0 (q 2)+2)) :=
    (hz.add_const 2).log (fun q => ne_of_gt (by positivity))
  have hL : Continuous (fun q : Fin 4 → ℝ => responseLog (max 0 (q 2))) := by
    exact hlog1.sub hlog2
  have htotal : Continuous (fun q : Fin 4 → ℝ => responseTotal e (q 1)) :=
    (hcoord 1).add ((responseA_continuous e).comp (hcoord 1))
  have hV : Continuous V := by
    dsimp [V,responsePotential]
    exact ((((((hcoord 1).mul hlog2).sub (htotal.mul hL)).add
      (p.continuousU.comp hz)).sub (((hcoord 3).const_mul 3).mul hL)).add
      (p.continuousP.comp (hcoord 1))).add (p.continuousR.comp (hcoord 3)) |>.add
      ((((hcoord 0).add (hcoord 1)).sub htotal).pow 2 |>.div_const 2)
  let K : Set (Fin 4 → ℝ) := Icc (fun _ => -384) (fun _ => 384)
  have hK : IsCompact K := isCompact_Icc
  obtain ⟨L,hLbound⟩ := hK.bddBelow_image hV.continuousOn
  obtain ⟨U,hUbound⟩ := hK.bddAbove_image hV.continuousOn
  refine ⟨L,U,?_⟩
  intro A B z H hA hA' hB hB' hz0 hz' hH hH'
  let q : Fin 4 → ℝ := ![A,B,z,H]
  have hq : q ∈ K := by
    constructor <;> intro i <;> fin_cases i <;> dsimp [q] <;> linarith
  have hb : L ≤ V q ∧ V q ≤ U := ⟨hLbound (mem_image_of_mem V hq), hUbound (mem_image_of_mem V hq)⟩
  change L ≤ responsePotential e p B (max 0 z) H (A+B-responseTotal e B) ∧
    responsePotential e p B (max 0 z) H (A+B-responseTotal e B) ≤ U at hb
  simpa only [max_eq_right hz0] using hb

end RobustPermanence

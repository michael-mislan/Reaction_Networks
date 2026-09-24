import proofs.RAFReactionQuotient.Resolution
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

noncomputable def sharpParameter (a : I) : I :=
  ⟨1-Real.sqrt (1-(a : ℝ)), by
    have hs := Real.sqrt_nonneg (1-(a : ℝ))
    have hsq := Real.sq_sqrt (show 0 ≤ 1-(a : ℝ) by linarith [a.property.2])
    constructor <;> nlinarith [a.property.1]⟩

theorem fibreParameter_sharp_le {R J : Type*} [Fintype R]
    (π : R → J) (a : I) (j : J)
    (hm : (Finset.univ.filter (fun r => π r = j)).card ≤ 2) :
    fibreParameter π (sharpParameter a) j ≤ a := by
  change (fibreParameter π (sharpParameter a) j : ℝ) ≤ (a : ℝ)
  rw [fibreParameter_value]
  have hs := Real.sqrt_nonneg (1-(a : ℝ))
  have hsq := Real.sq_sqrt (show 0 ≤ 1-(a : ℝ) by linarith [a.property.2])
  let m := (Finset.univ.filter (fun r => π r = j)).card
  change 1-(1-(1-Real.sqrt (1-(a : ℝ))))^m ≤ (a : ℝ)
  have hm' : m ≤ 2 := hm
  interval_cases m <;> norm_num <;> nlinarith [a.property.1,a.property.2]

theorem OR_sharp_domination {R J : Type*} [Fintype R] [Fintype J]
    (π : R → J) (a : I)
    (hm : ∀ j, (Finset.univ.filter (fun r => π r = j)).card ≤ 2)
    (E : (J → Prop) → Prop) (hE : Monotone E) :
    RAFEmergenceApprox.Generic.colLaw R (sharpParameter a) {ω | E (fieldOR π ω)} ≤
      (Measure.pi (fun _ : J => ambientCoordLaw a)) {ω | E ω} := by
  have he := fieldOR_map π (sharpParameter a)
  have hmap := Measure.map_apply (μ := RAFEmergenceApprox.Generic.colLaw R (sharpParameter a))
    (measurable_of_finite (fieldOR π)) ((Set.toFinite {ω | E ω}).measurableSet)
  rw [he] at hmap
  change (Measure.pi (fun j => ambientCoordLaw (fibreParameter π (sharpParameter a) j)))
    {ω | E ω} = RAFEmergenceApprox.Generic.colLaw R (sharpParameter a)
    {ω | E (fieldOR π ω)} at hmap
  rw [← hmap]
  exact product_increasing_mono _ _ (fun j => fibreParameter_sharp_le π a j (hm j)) E hE

theorem quotientSurvival_mono {a b : I} (hab : a ≤ b) :
    quotientSurvival a ≤ quotientSurvival b := by
  have hK (K : ℕ) :
      quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) ≤
      quotientStaticMeasure (2*(K+2)) b (quotientEscapeEvent 2 K) := by
    apply product_increasing_mono (fun _ => a) (fun _ => b) (fun _ => hab)
    intro x y hxy hx
    obtain ⟨w,hw,hl⟩ := hx
    refine ⟨w,quotientClosure_mono _ _ ?_ hw,hl⟩
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩
  exact le_of_tendsto_of_tendsto' (quotient_escape_tendsto a) (quotient_escape_tendsto b) hK

theorem split_sharp_survival_le_quotient (a : I) :
    staticSurvival (sharpParameter a) ≤ quotientSurvival a := by
  have hK (K : ℕ) :
      staticReactionMeasure (2*(K+2)) (sharpParameter a) (staticEscapeEvent 2 K) ≤
      quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
    let n := 2*(K+2)
    have h := OR_sharp_domination (@splitToQuotient n) a
      (fun j => by
        convert split_fibre_le_two j using 1
        congr 1
        ext r
        simp)
      (fun q => ∃ x ∈ quotientClosure n 2 (quotientOpen q), K+2 < (moleculeWord x).length) (by
        intro q r hqr hq
        obtain ⟨x,hx,hl⟩ := hq
        refine ⟨x,quotientClosure_mono n 2 ?_ hx,hl⟩
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqr j (Finset.mem_filter.mp hj).2⟩)
    simp only [quotientClosure_OR] at h
    simpa only [staticReactionMeasure,Measure.infinitePi_eq_pi,
      RAFEmergenceApprox.Generic.colLaw,staticEscapeEvent,quotientEscapeEvent,quotientStaticMeasure] using h
  exact le_of_tendsto_of_tendsto' (finite_static_escape_probability_tendsto (sharpParameter a))
    (quotient_escape_tendsto a) hK

theorem quotientTransitionLimit_mono {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
    quotientTransitionLimit x hx ≤ quotientTransitionLimit y hy := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply quotientSurvival_mono
  change 1-Real.exp (-x) ≤ 1-Real.exp (-y)
  have := Real.exp_le_exp.mpr (show -y ≤ -x by linarith)
  linarith

end RAFReactionQuotient

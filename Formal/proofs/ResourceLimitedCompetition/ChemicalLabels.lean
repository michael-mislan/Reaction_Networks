import proofs.ResourceLimitedCompetition.NutrientEndpoint

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

def chemicalLabelMatches (c : TaggedCell) : Prop :=
  if c.high then c.compartment.1 1 < 10*c.compartment.1 2
  else 10*c.compartment.1 2 < c.compartment.1 1

theorem safe_chemical_label (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (c : TaggedCell) (hm : 0 < c.compartment.2) (he : cellEnergy zL zH c < outerEnergy) :
    chemicalLabelMatches c := by
  have hmr : 0 < (c.compartment.2 : ℝ) := by exact_mod_cast hm
  have hz : ((c.compartment.1 2 : ℝ)/(c.compartment.2 : ℝ))*(c.compartment.2 : ℝ)=c.compartment.1 2 :=
    div_mul_cancel₀ _ (ne_of_gt hmr)
  have hB : ((c.compartment.1 1 : ℝ)/(c.compartment.2 : ℝ))*(c.compartment.2 : ℝ)=c.compartment.1 1 :=
    div_mul_cancel₀ _ (ne_of_gt hmr)
  cases hb : c.high with
  | false =>
    have henergy : lowEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zL) i) ≤ 1/32000000 := by
      simpa only [cellEnergy,hb,Bool.false_eq_true,if_false,outerEnergy] using he.le
    have hg := (low_safe_geometry zL hzL _ henergy).2
    have ht := mul_lt_mul_of_pos_right hg hmr
    simp only [concentration,sub_mul,mul_assoc,hz,hB,zero_mul] at ht
    simp only [chemicalLabelMatches,hb,Bool.false_eq_true,if_false]
    exact_mod_cast (show 10*(c.compartment.1 2 : ℝ) < (c.compartment.1 1 : ℝ) by linarith only [ht])
  | true =>
    have henergy : highEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zH) i) ≤ 1/32000000 := by
      simpa only [cellEnergy,hb,if_true,outerEnergy] using he.le
    have hg := (high_safe_geometry zH hzH _ henergy).2
    have ht := mul_lt_mul_of_pos_right hg hmr
    simp only [concentration,sub_mul,mul_assoc,hz,hB,zero_mul] at ht
    simp only [chemicalLabelMatches,hb,if_true]
    exact_mod_cast (show (c.compartment.1 1 : ℝ) < 10*(c.compartment.1 2 : ℝ) by linarith only [ht])

theorem nutrient_chemical_labels (N M : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (e : PopulationEvent (activeDomain N M zL zH)) (hn : eventReason N M zL zH e=.nutrient) :
    ∀ c ∈ (eventOutcome N e).live, chemicalLabelMatches c := by
  have hs := activeDomain_safe N M zL zH e.1.val e.1.property
  have hv := event_valid_volumes N hN _ e.1 e.2 hs.2.2.2.2.1
  have he := nutrient_event_energy N M zL zH _ e.1 e.2 hs.2.2.2.2.2 hn
  intro c hc
  exact safe_chemical_label zL zH hzL hzH c (hN.trans_le (hv c hc).1) (he c hc)

end ResourceLimitedCompetition

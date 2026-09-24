import proofs.AssayInformation.DensitySigns

noncomputable section
namespace AssayInformation
open DiagnosticWindows MeasureTheory Set

def timingBlank (φ : ℝ → ℝ) : ℝ := ∫ t in Ioi 0, φ t*blankDensity t
def timingMiss (φ : ℝ → ℝ) : ℝ :=
  1-((1-miss5 0)*φ 0+∫ t in Ioi 0, φ t*loadedDensity t)

theorem bounded_test_integrable (f φ : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (hm : Measurable φ) (hφ : ∀ t, φ t ∈ Icc 0 1) :
    IntegrableOn (fun t => φ t*f t) (Ioi 0) := by
  apply hf.bdd_mul hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  simpa [Real.norm_eq_abs,abs_of_nonneg (hφ t).1] using (hφ t).2

theorem prefix_integral (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    (a : ℝ) (ha : 0 ≤ a) :
    (∫ t in Ioc 0 a, f t) = (∫ t in Ioi 0, f t)-(∫ t in Ioi a, f t) := by
  rw [← Ioi_diff_Ioi]
  exact setIntegral_diff measurableSet_Ioi hf (fun _ ht => ha.trans_lt ht)

theorem prefix_indicator_integral (f : ℝ → ℝ) (a : ℝ) :
    (∫ t in Ioi 0, (Ioc 0 a).indicator f t) = ∫ t in Ioc 0 a, f t := by
  rw [setIntegral_indicator measurableSet_Ioc,inter_eq_right.mpr]
  intro t ht
  exact ht.1

theorem timing_dual (φ : ℝ → ℝ) (hm : Measurable φ)
    (hφ : ∀ t, φ t ∈ Icc 0 1) :
    miss5 5-5*(timingBlank φ-blank5 4) ≤ timingMiss φ := by
  have hb : IntegrableOn blankDensity (Ioi 0) := suffixDensity_integrable 0 0
  have hl := loadedDensity_integrable 0
  have hp0 := bounded_test_integrable blankDensity φ hb hm hφ
  have hp1 := bounded_test_integrable loadedDensity φ hl hm hφ
  have hi0 : IntegrableOn ((Ioc (0:ℝ) 4).indicator blankDensity) (Ioi 0) :=
    hb.indicator measurableSet_Ioc
  have hi1 : IntegrableOn ((Ioc (0:ℝ) 5).indicator loadedDensity) (Ioi 0) :=
    hl.indicator measurableSet_Ioc
  have pointwise (t : ℝ) (ht : t ∈ Ioi (0:ℝ)) :
      φ t*loadedDensity t ≤ 5*(φ t*blankDensity t)+
        (Ioc 0 5).indicator loadedDensity t-5*(Ioc 0 4).indicator blankDensity t := by
    have hf0 : 0 ≤ blankDensity t := suffixDensity_nonneg 0 ⟨t,ht.le⟩
    have hf1 : 0 ≤ loadedDensity t := loadedDensity_nonneg ⟨t,ht.le⟩
    obtain ⟨h0,h1⟩ := hφ t
    by_cases ht4 : t ≤ 4
    · have ht5 : t ≤ 5 := by linarith
      simp only [indicator_of_mem (show t ∈ Ioc (0:ℝ) 5 from ⟨ht,ht5⟩),
        indicator_of_mem (show t ∈ Ioc (0:ℝ) 4 from ⟨ht,ht4⟩)]
      have hd := early_density_order t ⟨ht.le,ht4⟩
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hd)]
    · have hn4 : t ∉ Ioc (0:ℝ) 4 := fun h => ht4 h.2
      by_cases ht5 : t ≤ 5
      · simp only [indicator_of_mem (show t ∈ Ioc (0:ℝ) 5 from ⟨ht,ht5⟩),
          indicator_of_notMem hn4,mul_zero,sub_zero]
        nlinarith [mul_nonneg h0 hf0,mul_nonneg (sub_nonneg.mpr h1) hf1]
      · have hn5 : t ∉ Ioc (0:ℝ) 5 := fun h => ht5 h.2
        simp only [indicator_of_notMem hn4,indicator_of_notMem hn5,mul_zero,sub_zero,add_zero]
        have hd := late_density_order t (by linarith)
        nlinarith [mul_nonneg h0 (sub_nonneg.mpr hd)]
  have hbound := setIntegral_mono_on hp1 ((hp0.const_mul 5).add hi1 |>.sub (hi0.const_mul 5))
    measurableSet_Ioi pointwise
  simp only [Pi.sub_apply,Pi.add_apply] at hbound
  have heq := integral_sub ((hp0.const_mul 5).add hi1) (hi0.const_mul 5)
  have heqa := integral_add (hp0.const_mul 5) hi1
  simp only [Pi.add_apply] at heq
  rw [heq,heqa,integral_const_mul,integral_const_mul,
      prefix_indicator_integral,prefix_indicator_integral,
      prefix_integral loadedDensity hl 5 (by norm_num),
      prefix_integral blankDensity hb 4 (by norm_num)] at hbound
  have hl0 := loadedDensity_tail_source 0
  have hl5 := loadedDensity_tail_source 5
  have hb4 := blankDensity_tail_source 4
  norm_num only [NNReal.coe_zero,NNReal.coe_ofNat] at hl0 hl5 hb4
  rw [hl0,hl5,blankDensity_total,hb4] at hbound
  have hatom := mul_le_of_le_one_right loaded_atom_nonneg (hφ 0).2
  unfold timingBlank timingMiss
  linarith

end AssayInformation

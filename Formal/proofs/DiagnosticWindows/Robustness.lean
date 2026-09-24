import proofs.DiagnosticWindows.RateScale
import proofs.DiagnosticWindows.Windows

namespace DiagnosticWindows
open FiniteCopy

theorem slow10_valid (z : Fin 6) : (49/50:ℝ)*rates10 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates10]

theorem fast10_valid (z : Fin 6) : (51/50:ℝ)*rates10 z ∈ Set.Icc 0 1 := by
  fin_cases z <;> norm_num [rates10]

theorem uncertainty_valid (r : Fin 6 → ℝ)
    (h : ∀ z, (49/50:ℝ)*rates10 z ≤ r z ∧ r z ≤ (51/50:ℝ)*rates10 z)
    (z : Fin 6) : r z ∈ Set.Icc 0 1 :=
  ⟨(slow10_valid z).1.trans (h z).1,(h z).2.trans (fast10_valid z).2⟩

/-- Uniform guarantee for every fixed state-specific rate vector in the box,
every load at least 3.99, and every actual time in [3.19,3.21]. -/
theorem robust_guarantee (r : Fin 6 → ℝ)
    (h : ∀ z, (49/50:ℝ)*rates10 z ≤ r z ∧ r z ≤ (51/50:ℝ)*rates10 z)
    (load t : NNReal) (hl : 399/100 ≤ load)
    (ht0 : 319/100 ≤ t) (ht1 : t ≤ 321/100) :
    (1-(birthKernel r (uncertainty_valid r h)).poissonized ((5/2)*t) uncalled 0 ≤ 1/100) ∧
    loadedSurvival (birthKernel r (uncertainty_valid r h)) load ((5/2)*t) ≤ 1/20 := by
  constructor
  · have ho := birth_survival_order r (fun z => (51/50:ℝ)*rates10 z)
      (uncertainty_valid r h) fast10_valid (fun z => (h z).2) ((5/2)*t) 0
    have hscale := scaled_survival rates10 rates10_valid modes10 eigen10 capacity10_sum capacity10_eigen
      (51/50) fast10_valid ((5/2)*t) 0
    norm_num at hscale
    rw [hscale] at ho
    have he : (51/50:NNReal)*((5/2)*t) = (5/2)*((51/50)*t) := by ring
    rw [he] at ho
    have ht : (51/50:NNReal)*t ≤ 16371/5000 := by nlinarith
    have hb := (blank10_monotone ht).trans robust_blank_blank_bound
    unfold blank10 kernel10 at hb
    linarith
  · have hlm := loading_antitone r (uncertainty_valid r h) ((5/2)*t) hl
    have ho := loaded_rate_order (fun z => (49/50:ℝ)*rates10 z) r slow10_valid
      (uncertainty_valid r h) (fun z => (h z).1) (399/100) ((5/2)*t)
    have hscale := scaled10_loading (49/50) slow10_valid (399/100) ((5/2)*t)
    norm_num at hscale
    rw [hscale] at ho
    have he : (49/50:NNReal)*((5/2)*t) = (5/2)*((49/50)*t) := by ring
    rw [he] at ho
    have ht : (15631/5000:NNReal) ≤ (49/50)*t := by nlinarith
    exact hlm.trans (ho.trans ((loaded10_antitone (399/100) ht).trans robust_miss_miss_bound))

end DiagnosticWindows

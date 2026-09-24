import proofs.SandwichImmunoassay.Main

namespace SandwichImmunoassay

theorem excludes_low (s : Specimen) (hz : 1/5000  <  s.contrast) : 1/10  <  s.x :=  by
  by_contra h
  have :=  contrast_low s (le_of_not_gt h)
  linarith

theorem excludes_high_band (s : Specimen) (hz : s.contrast  <  1/1000) :
    ¬ (25  ≤  s.x ∧ s.x  ≤  100) :=  by
  rintro ⟨h0,h1⟩
  have :=  contrast_high s h0 h1
  linarith

theorem identifies_guard_band (s : Specimen) (hu : s.x  ≤  100)
    (ha : 1/5000  <  s.contrast) (hb : s.contrast  <  1/1000) :
    1/10  <  s.x ∧ s.x  <  25 :=  by
  refine ⟨excludes_low s ha, ?_⟩
  by_contra h
  exact excludes_high_band s hb ⟨le_of_not_gt h,hu⟩

def compatibleWithin (U a b : ℝ) : Set ℝ :=  compatible a b ∩ Set.Icc 0 U

theorem truth_within (s : Specimen) {U : ℝ} (hu : s.x  ≤  U) :
    s.x ∈ compatibleWithin U s.y1 s.yd := 
  ⟨truth_contained s,s.x_nonneg,hu⟩

end SandwichImmunoassay

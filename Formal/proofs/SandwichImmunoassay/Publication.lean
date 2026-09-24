import proofs.SandwichImmunoassay.Consequences
import proofs.SandwichImmunoassay.Preparation

namespace SandwichImmunoassay

theorem stronger_contrast (s : Specimen) (hx0 : 25 ≤ s.x) (hx1 : s.x ≤ 100) :
    199/5000 ≤ s.contrast := by
  have u := native_high hx0 hx1 s.rho_lo s.rho_hi
  have source := stronger_margin_source s.neat s.diluted s.c_box s.d_box s.k_box s.j_box
    u.1 u.2 s.dilution_lo s.dilution_hi s.drift_lo
  have noise := noisy_margin s.gain_lo (by norm_num : (0:ℝ) ≤ 1)
    (by norm_num : (0:ℝ) ≤ 1/25) source s.error_neat s.error_diluted
  change 199/5000 ≤ (s.g*s.r*signal (s.rho*s.x/s.d) s.pd s.qd+s.ed)-
    (s.g*signal (s.rho*s.x) s.p s.q+s.e1)
  linarith only [noise]

theorem publication_main :
    (∀ s : Specimen, s.x ≤ 1/10 → s.contrast ≤ 1/5000) ∧
    (∀ s : Specimen, 25 ≤ s.x → s.x ≤ 100 → 199/5000 ≤ s.contrast) ∧
    (∀ s : Specimen, s.x ≤ 100 → 1/5000 < s.contrast → s.contrast < 199/5000 →
      1/10 < s.x ∧ s.x < 25) := by
  refine ⟨contrast_low,stronger_contrast,?_⟩
  intro s hu ha hb
  refine ⟨excludes_low s ha,?_⟩
  by_contra hn
  have := stronger_contrast s (le_of_not_gt hn) hu
  linarith only [this,hb]

end SandwichImmunoassay

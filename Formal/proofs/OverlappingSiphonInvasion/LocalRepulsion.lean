import proofs.OverlappingSiphonInvasion.ResidentInvasion

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

private theorem local_column_margin (y : State) (f g : State → ℝ)
    (hf : Continuous f) (hg : Continuous g) (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (h1 : 2*δ ≤ f y) (h2 : 2*δ*r ≤ g y) :
    ∀ᶠ x in 𝓝 y, δ ≤ f x ∧ δ*r ≤ g x := by
  have h1' : δ < f y := by linarith
  have h2' : δ*r < g y := by nlinarith [mul_pos hδ hr]
  filter_upwards [hf.continuousAt.eventually_const_lt h1',
    hg.continuousAt.eventually_const_lt h2'] with x hx1 hx2
  exact ⟨hx1.le,hx2.le⟩

/-- Strict invasion of the source-derived first resident block gives a single
positive linear missing-species mass with uniformly positive relative drift
throughout a neighborhood, including its nonnegative boundary. -/
theorem resident1_local_repulsion (p : Rates) (s u : ℝ)
    (hB : 0 < p.beta2*s) (hC : 0 < (p.gamma1+p.gamma2)*u)
    (hinv : 0 ≤ p.alpha2*s-p.gamma2*u-p.mu2 ∨
      0 ≤ p.eta1*u+p.alpha3*s-p.mu3 ∨
      (p.alpha2*s-p.gamma2*u-p.mu2)*(p.eta1*u+p.alpha3*s-p.mu3) <
        (p.beta2*s)*((p.gamma1+p.gamma2)*u)) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ᶠ x in 𝓝 (face1 s u), 0 ≤ x 2 → 0 ≤ x 3 →
        δ*(x 2+r*x 3) ≤ field p x 2+r*field p x 3 := by
  obtain ⟨r,δ,hr,hδ,h1,h2⟩ := positive_covector_margin _ _ _ _ hB hC hinv
  let f : State → ℝ := fun x =>
    p.alpha2*x 0-p.gamma2*x 1-p.mu2-p.eta2*x 3+r*(p.gamma1+p.gamma2)*x 1
  let g : State → ℝ := fun x =>
    p.beta2*x 0+r*(p.eta1*x 1+p.alpha3*x 0-p.mu3+p.eta2*x 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : 2*δ ≤ f (face1 s u) := by simpa [f,face1,mul_assoc] using h1
  have hg0 : 2*δ*r ≤ g (face1 s u) := by simpa [g,face1] using h2
  refine ⟨r,δ,hr,hδ,?_⟩
  filter_upwards [local_column_margin _ f g hf hg r δ hr hδ hf0 hg0] with x hx
  intro hb hc
  have hb' := mul_le_mul_of_nonneg_right hx.1 hb
  have hc' := mul_le_mul_of_nonneg_right hx.2 hc
  have hid : field p x 2+r*field p x 3 = f x*x 2+g x*x 3 := by
    simp [field,f,g]
    ring
  rw [hid]
  nlinarith only [hb',hc']

theorem resident2_local_repulsion (p : Rates) (s u : ℝ)
    (hB : 0 < p.beta1*s) (hC : 0 < (p.gamma1+p.gamma2)*u)
    (hinv : 0 ≤ p.alpha1*s-p.gamma1*u-p.mu1 ∨
      0 ≤ p.eta2*u+p.alpha3*s-p.mu3 ∨
      (p.alpha1*s-p.gamma1*u-p.mu1)*(p.eta2*u+p.alpha3*s-p.mu3) <
        (p.beta1*s)*((p.gamma1+p.gamma2)*u)) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ᶠ x in 𝓝 (face2 s u), 0 ≤ x 1 → 0 ≤ x 3 →
        δ*(x 1+r*x 3) ≤ field p x 1+r*field p x 3 := by
  obtain ⟨r,δ,hr,hδ,h1,h2⟩ := positive_covector_margin _ _ _ _ hB hC hinv
  let f : State → ℝ := fun x =>
    p.alpha1*x 0-p.gamma1*x 2-p.mu1-p.eta1*x 3+r*(p.gamma1+p.gamma2)*x 2
  let g : State → ℝ := fun x =>
    p.beta1*x 0+r*(p.eta2*x 2+p.alpha3*x 0-p.mu3+p.eta1*x 1)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hf0 : 2*δ ≤ f (face2 s u) := by simpa [f,face2,mul_assoc] using h1
  have hg0 : 2*δ*r ≤ g (face2 s u) := by simpa [g,face2] using h2
  refine ⟨r,δ,hr,hδ,?_⟩
  filter_upwards [local_column_margin _ f g hf hg r δ hr hδ hf0 hg0] with x hx
  intro ha hc
  have ha' := mul_le_mul_of_nonneg_right hx.1 ha
  have hc' := mul_le_mul_of_nonneg_right hx.2 hc
  have hid : field p x 1+r*field p x 3 = f x*x 1+g x*x 3 := by
    simp [field,f,g]
    ring
  rw [hid]
  nlinarith only [ha',hc']

end OverlappingSiphonInvasion

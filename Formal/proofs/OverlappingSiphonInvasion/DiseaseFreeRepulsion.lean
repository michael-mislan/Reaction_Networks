import proofs.OverlappingSiphonInvasion.LocalRepulsion

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

/-- The disease-free normal block may be reducible and its shared-species
diagonal may be negative. Positive growth of both single strains and positive
production from the shared species still yield a growing positive covector. -/
theorem diseaseFree_local_repulsion (p : Rates) (s : ℝ)
    (ha : 0 < p.alpha1*s-p.mu1) (hb : 0 < p.alpha2*s-p.mu2)
    (hk : 0 < (p.beta1+p.beta2)*s) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ᶠ x in 𝓝 (face1 s 0), (∀ i, 0 ≤ x i) →
        δ*(x 1+x 2+r*x 3) ≤ field p x 1+field p x 2+r*field p x 3 := by
  obtain ⟨r,hr,_,hc⟩ :=
    (positive_covector_iff 1 ((p.beta1+p.beta2)*s) 1 (p.alpha3*s-p.mu3)
      hk (by norm_num)).mpr (Or.inl (by norm_num))
  let A := p.alpha1*s-p.mu1
  let B := p.alpha2*s-p.mu2
  let C := (p.beta1+p.beta2)*s+r*(p.alpha3*s-p.mu3)
  let δ := min A (min B (C/r))/2
  have hδ : 0 < δ := by
    exact div_pos (lt_min ha (lt_min hb (div_pos hc hr))) (by norm_num)
  have hδa : δ < A := by
    have hh := min_le_left A (min B (C/r))
    dsimp [δ] at hδ ⊢
    linarith
  have hδb : δ < B := by
    have hh := (min_le_right A (min B (C/r))).trans (min_le_left B (C/r))
    dsimp [δ] at hδ ⊢
    linarith
  have hδc : δ*r < C := by
    have hh := (min_le_right A (min B (C/r))).trans (min_le_right B (C/r))
    have hh' := (le_div_iff₀ hr).mp hh
    have hm := mul_pos hδ hr
    dsimp [δ] at hm ⊢
    nlinarith only [hh',hm]
  let f : State → ℝ := fun x => p.alpha1*x 0-p.mu1-p.gamma1*x 2-p.eta1*x 3+
    r*p.gamma1*x 2+r*p.eta1*x 3
  let g : State → ℝ := fun x => p.alpha2*x 0-p.mu2-p.gamma2*x 1-p.eta2*x 3+
    r*p.gamma2*x 1+r*p.eta2*x 3
  let k : State → ℝ := fun x => (p.beta1+p.beta2)*x 0+r*(p.alpha3*x 0-p.mu3)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hfa : δ < f (face1 s 0) := by simpa [f,face1,A] using hδa
  have hgb : δ < g (face1 s 0) := by simpa [g,face1,B] using hδb
  have hkc' : δ*r < k (face1 s 0) := by simpa [k,face1,C] using hδc
  refine ⟨r,δ,hr,hδ,?_⟩
  filter_upwards [hf.continuousAt.eventually_const_lt hfa,
    hg.continuousAt.eventually_const_lt hgb,
    hkc.continuousAt.eventually_const_lt hkc'] with x hx1 hx2 hx3
  intro hx
  have h1 := mul_le_mul_of_nonneg_right hx1.le (hx 1)
  have h2 := mul_le_mul_of_nonneg_right hx2.le (hx 2)
  have h3 := mul_le_mul_of_nonneg_right hx3.le (hx 3)
  have hid : field p x 1+field p x 2+r*field p x 3 =
      f x*x 1+g x*x 2+k x*x 3 := by
    simp [field,f,g,k]
    ring
  rw [hid]
  nlinarith only [h1,h2,h3]

end OverlappingSiphonInvasion

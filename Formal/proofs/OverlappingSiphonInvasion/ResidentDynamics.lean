import proofs.OverlappingSiphonInvasion.ResidentConvergence
import proofs.CoreCouplingGlobal.ScalarComparison

noncomputable section
open Filter Topology
namespace OverlappingSiphonInvasion

/-- Every positive global resident solution converges to its endemic equilibrium.
All bounds are derived from recruitment and mortality, including unequal deaths. -/
theorem resident_positive_converges (Λ α μ₀ μ se ue : ℝ) (s u : ℝ → ℝ)
    (hΛ : 0 < Λ) (hα : 0 < α) (hμ₀ : 0 < μ₀) (hμ : 0 < μ)
    (hse : 0 < se) (hue : 0 < ue)
    (hbalance : Λ = (μ₀+α*ue)*se) (hdeath : μ = α*se)
    (hpos : ∀ t, 0 ≤ t → 0 < s t ∧ 0 < u t)
    (hds : ∀ t, 0 ≤ t → HasDerivAt s (Λ-μ₀*s t-α*s t*u t) t)
    (hdu : ∀ t, 0 ≤ t → HasDerivAt u (u t*(α*s t-μ)) t) :
    Tendsto s atTop (𝓝 se) ∧ Tendsto u atTop (𝓝 ue) := by
  let m := min μ₀ μ
  have hm : 0 < m := lt_min hμ₀ hμ
  let M := Λ/m+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hNd : ∀ t, 0 ≤ t → HasDerivAt (fun t => s t+u t)
      (Λ-μ₀*s t-μ*u t) t := by
    intro t ht
    convert (hds t ht).add (hdu t ht) using 1
    ring
  have hNb : ∀ t, 0 ≤ t → Λ-μ₀*s t-μ*u t ≤ Λ-m*(s t+u t) := by
    intro t ht
    have h1 := mul_le_mul_of_nonneg_right (min_le_left μ₀ μ) (hpos t ht).1.le
    have h2 := mul_le_mul_of_nonneg_right (min_le_right μ₀ μ) (hpos t ht).2.le
    dsimp [m]
    nlinarith only [h1,h2]
  have hupper := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => s t+u t) (fun t => Λ-μ₀*s t-μ*u t) 0 Λ m M hm
    (by dsimp [M]; linarith) hNd hNb
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hupper.and (eventually_ge_atTop (0:ℝ)))
  have hT0 : 0 ≤ T := (hT T le_rfl).2
  let k := μ₀+α*M
  have hk : 0 < k := by dsimp [k]; positivity
  let l := (Λ/k)/2
  have hl : 0 < l := by dsimp [l]; positivity
  have hlow := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => -s t) (fun t => -(Λ-μ₀*s t-α*s t*u t)) T (-Λ) k (-l) hk
    (by dsimp [l]; rw [neg_div]; linarith [div_pos hΛ hk])
    (fun t ht => (hds t (hT0.trans ht)).neg)
    (by
      intro t ht
      have hs := (hpos t (hT0.trans ht)).1
      have huM : u t ≤ M := by have hh := (hT t ht).1; linarith
      have hm' := mul_le_mul_of_nonneg_left huM (mul_pos hα hs).le
      dsimp [k]
      nlinarith only [hm'])
  obtain ⟨T',hT'⟩ := eventually_atTop.1
    ((hlow.and hupper).and (eventually_ge_atTop (0:ℝ)))
  apply resident_converges_of_box se ue α μ₀ M l T' s u hse hue hα hμ₀ hM hl
  · intro t ht
    have hp := hpos t (hT' t ht).2
    have hb := (hT' t ht).1
    exact ⟨hp.1,hp.2,by linarith [hb.1],by linarith [hb.2],by linarith [hb.2]⟩
  · intro t ht
    convert hds t (hT' t ht).2 using 1
    rw [hbalance]
    ring
  · intro t ht
    convert hdu t (hT' t ht).2 using 1
    rw [hdeath]
    ring

theorem diseaseFree_converges (Λ μ₀ : ℝ) (s : ℝ → ℝ) (hμ : 0 < μ₀)
    (hd : ∀ t, 0 ≤ t → HasDerivAt s (Λ-μ₀*s t) t) :
    Tendsto s atTop (𝓝 (Λ/μ₀)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hu := CoreCouplingGlobal.eventual_upper_of_linear_drift
    s (fun t => Λ-μ₀*s t) 0 Λ μ₀ (Λ/μ₀+ε) hμ (by linarith) hd
    (fun _ _ => le_rfl)
  have hl := CoreCouplingGlobal.eventual_upper_of_linear_drift
    (fun t => -s t) (fun t => -(Λ-μ₀*s t)) 0 (-Λ) μ₀ (-Λ/μ₀+ε) hμ
    (by linarith) (fun t ht => (hd t ht).neg)
    (fun t _ => by ring_nf; exact le_rfl)
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hu.and hl)
  refine ⟨T,?_⟩
  intro t ht
  have hh := hT t ht
  rw [Real.dist_eq,abs_lt]
  rw [neg_div] at hh
  constructor <;> linarith [hh.1,hh.2]

end OverlappingSiphonInvasion

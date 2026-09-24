import proofs.CoreCouplingGlobal.NonlinearQuadratic
import proofs.CoreCouplingGlobal.ConeEscape

namespace CoreCouplingGlobal
open Set

def spectralQuadratic (v : SaddleVector) : ℝ :=
  (v 0)^2+(v 1)^2+(v 2)^2-(v 3)^2

noncomputable def spectralGradient : SaddleVector →L[ℝ] SaddleVector :=
  ContinuousLinearMap.pi fun i => (if i=3 then (-2:ℝ) else 2) •
    ContinuousLinearMap.proj i

noncomputable def spectralLinear (μ : Fin 4 → ℝ) : SaddleVector →L[ℝ] SaddleVector :=
  ContinuousLinearMap.pi fun i => μ i • ContinuousLinearMap.proj i

theorem spectral_bilinear_hasStrictFDerivAt (μ : Fin 4 → ℝ)
    (B : SaddleVector →L[ℝ] SaddleVector →L[ℝ] SaddleVector) :
    HasStrictFDerivAt (fun x => spectralLinear μ x+B x x) (spectralLinear μ) 0 := by
  have hb : HasStrictFDerivAt (fun x : SaddleVector => B x x)
      (0 : SaddleVector →L[ℝ] SaddleVector) 0 := by
    simpa using B.hasStrictFDerivAt_of_bilinear
      ((ContinuousLinearMap.id ℝ SaddleVector).hasStrictFDerivAt (x := (0:SaddleVector)))
      ((ContinuousLinearMap.id ℝ SaddleVector).hasStrictFDerivAt (x := (0:SaddleVector)))
  simpa using (spectralLinear μ).hasStrictFDerivAt.add hb

theorem spectralQuadratic_lower (v : SaddleVector) : -‖v‖^2 ≤ spectralQuadratic v := by
  have h := norm_le_pi_norm v (3 : Fin 4)
  rw [Real.norm_eq_abs] at h
  have hn := norm_nonneg v
  have ha := abs_nonneg (v 3)
  have hs := sq_abs (v 3)
  dsimp [spectralQuadratic]
  nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]

theorem spectralQuadratic_hasDerivAt (X : ℝ → SaddleVector) (dX : SaddleVector)
    (t : ℝ) (hd : HasDerivAt X dX t) :
    HasDerivAt (fun u => spectralQuadratic (X u))
      (saddlePairing (spectralGradient (X t)) dX) t := by
  have h0 := (hasDerivAt_pi.mp hd (0 : Fin 4)).pow 2
  have h1 := (hasDerivAt_pi.mp hd (1 : Fin 4)).pow 2
  have h2 := (hasDerivAt_pi.mp hd (2 : Fin 4)).pow 2
  have h3 := (hasDerivAt_pi.mp hd (3 : Fin 4)).pow 2
  convert ((h0.add h1).add h2).sub h3 using 1
  simp [spectralGradient,saddlePairing,Fin.sum_univ_succ]
  ring

theorem spectral_linear_dissipation (μ : Fin 4 → ℝ)
    (hs : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) (hu : 0 < μ 3) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ v : SaddleVector,
      saddlePairing (spectralGradient v) (spectralLinear μ v) ≤ -(κ*‖v‖^2) := by
  let κ := min (1:ℝ) (μ 3)
  have hκ : 0 < κ := lt_min (by norm_num) hu
  have hk1 : κ ≤ 1 := min_le_left _ _
  have hku : κ ≤ μ 3 := min_le_right _ _
  have h0 : μ 0 < -(1/2:ℝ) := hs 0
  have h1 : μ 1 < -(1/2:ℝ) := hs 1
  have h2 : μ 2 < -(1/2:ℝ) := hs 2
  refine ⟨κ,hκ,?_⟩
  intro v
  have hrate0 := mul_le_mul_of_nonneg_right (show 2*μ 0 ≤ -κ by linarith) (sq_nonneg (v 0))
  have hrate1 := mul_le_mul_of_nonneg_right (show 2*μ 1 ≤ -κ by linarith) (sq_nonneg (v 1))
  have hrate2 := mul_le_mul_of_nonneg_right (show 2*μ 2 ≤ -κ by linarith) (sq_nonneg (v 2))
  have hrate3 := mul_le_mul_of_nonneg_right (show -2*μ 3 ≤ -κ by linarith) (sq_nonneg (v 3))
  have hnorm := mul_le_mul_of_nonneg_left (saddle_vector_norm_sq_le v) hκ.le
  simp [spectralGradient,spectralLinear,saddlePairing,Fin.sum_univ_succ]
  nlinarith only [hrate0,hrate1,hrate2,hrate3,hnorm]

/-- There is at most one forever-locally-trapped trajectory initial state over
each stable projection. This requires no decay hypothesis on either trajectory. -/
theorem spectral_trapped_initial_unique (f : SaddleVector → SaddleVector)
    (μ : Fin 4 → ℝ) (hd : HasStrictFDerivAt f (spectralLinear μ) 0)
    (hs : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) (hu : 0 < μ 3) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : ℝ → SaddleVector,
      (∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t) →
      (∀ t, 0 ≤ t → HasDerivAt Y (f (Y t)) t) →
      (∀ t, 0 ≤ t → dist (X t) 0 < δ) →
      (∀ t, 0 ≤ t → dist (Y t) 0 < δ) →
      (∀ i : Fin 3, X 0 i.castSucc=Y 0 i.castSucc) → X 0=Y 0 := by
  obtain ⟨κ,hκ,hlin⟩ := spectral_linear_dissipation μ hs hu
  obtain ⟨δ,hδ,hpair⟩ := strict_linear_dissipation_persists
    f spectralGradient (spectralLinear μ) 0 hd κ hκ hlin
  refine ⟨δ,hδ,?_⟩
  intro X Y hX hY hXt hYt hstable
  by_contra hne
  have hu0 : X 0 3 ≠ Y 0 3 := by
    intro h
    apply hne
    ext i
    fin_cases i
    · exact hstable 0
    · exact hstable 1
    · exact hstable 2
    · exact h
  let q := fun t => spectralQuadratic (X t-Y t)
  let dq := fun t => saddlePairing (spectralGradient (X t-Y t)) (f (X t)-f (Y t))
  let N := fun t => ‖X t-Y t‖^2
  have hq0 : q 0 < 0 := by
    have h0 := hstable 0
    have h1 := hstable 1
    have h2 := hstable 2
    change X 0 0=Y 0 0 at h0
    change X 0 1=Y 0 1 at h1
    change X 0 2=Y 0 2 at h2
    have heq : q 0=-(X 0 3-Y 0 3)^2 := by
      simp [q,spectralQuadratic,h0,h1,h2]
    rw [heq]
    exact neg_neg_of_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hu0))
  have hqd : ∀ t, 0 ≤ t → HasDerivAt q (dq t) t := by
    intro t ht
    exact spectralQuadratic_hasDerivAt (fun u => X u-Y u) _ t ((hX t ht).sub (hY t ht))
  have hbound : ∀ t, 0 ≤ t → -(4*δ^2) ≤ q t := by
    intro t ht
    have hxn : ‖X t‖ < δ := by simpa using hXt t ht
    have hyn : ‖Y t‖ < δ := by simpa using hYt t ht
    have hdiff := norm_sub_le (X t) (Y t)
    have hn := norm_nonneg (X t-Y t)
    have hlow := spectralQuadratic_lower (X t-Y t)
    dsimp [q]
    nlinarith
  have hdec : ∀ t, 0 ≤ t → dq t ≤ -(κ/2)*N t := by
    intro t ht
    have hh := hpair (X t) (Y t) (hXt t ht) (hYt t ht)
    dsimp [dq,N]
    linarith only [hh]
  exact negative_quadratic_not_globally_bounded q dq N 1 (κ/2) (4*δ^2)
    (by norm_num) (by positivity) (by positivity) hqd
    (fun t _ => sq_nonneg _) (fun t _ => by simpa [N,q] using spectralQuadratic_lower (X t-Y t))
    hdec hbound hq0

end CoreCouplingGlobal

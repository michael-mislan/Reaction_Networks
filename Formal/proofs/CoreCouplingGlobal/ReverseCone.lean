import proofs.CoreCouplingGlobal.SpectralCone

namespace CoreCouplingGlobal
open Set

theorem negative_spectralQuadratic_lower (v : SaddleVector) :
    -(3*‖v‖^2) ≤ -spectralQuadratic v := by
  have hsq : ∀ i : Fin 4, (v i)^2 ≤ ‖v‖^2 := by
    intro i
    have hh := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at hh
    nlinarith [sq_abs (v i),abs_nonneg (v i),norm_nonneg v]
  dsimp [spectralQuadratic]
  nlinarith [hsq 0,hsq 1,hsq 2,sq_nonneg (v 3)]

/-- For reversed dynamics, prescribing the original unstable coordinate
uniquely determines any trajectory that stays near the saddle forever. -/
theorem reversed_spectral_trapped_initial_unique (f : SaddleVector → SaddleVector)
    (μ : Fin 4 → ℝ) (hd : HasStrictFDerivAt f (spectralLinear μ) 0)
    (hs : ∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) (hu : 0 < μ 3) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X Y : ℝ → SaddleVector,
      (∀ t, 0 ≤ t → HasDerivAt X (-f (X t)) t) →
      (∀ t, 0 ≤ t → HasDerivAt Y (-f (Y t)) t) →
      (∀ t, 0 ≤ t → dist (X t) 0 < δ) →
      (∀ t, 0 ≤ t → dist (Y t) 0 < δ) →
      X 0 3=Y 0 3 → X 0=Y 0 := by
  obtain ⟨κ,hκ,hlin⟩ := spectral_linear_dissipation μ hs hu
  have hlin' : ∀ v : SaddleVector,
      saddlePairing ((-spectralGradient) v) ((-spectralLinear μ) v) ≤ -(κ*‖v‖^2) := by
    intro v
    simpa [saddlePairing] using hlin v
  obtain ⟨δ,hδ,hpair⟩ := strict_linear_dissipation_persists
    (fun x => -f x) (-spectralGradient) (-spectralLinear μ) 0 hd.neg κ hκ hlin'
  refine ⟨δ,hδ,?_⟩
  intro X Y hX hY hXt hYt hstable
  by_contra hne
  let q := fun t => -spectralQuadratic (X t-Y t)
  let dq := fun t => -saddlePairing (spectralGradient (X t-Y t)) (-f (X t)- -f (Y t))
  let N := fun t => ‖X t-Y t‖^2
  have hq0 : q 0 < 0 := by
    have hsumpos : 0 < (X 0 0-Y 0 0)^2+(X 0 1-Y 0 1)^2+(X 0 2-Y 0 2)^2 := by
      by_contra hn
      have h0 : X 0 0=Y 0 0 := by
        nlinarith [sq_nonneg (X 0 0-Y 0 0),sq_nonneg (X 0 1-Y 0 1),sq_nonneg (X 0 2-Y 0 2)]
      have h1 : X 0 1=Y 0 1 := by
        nlinarith [sq_nonneg (X 0 0-Y 0 0),sq_nonneg (X 0 1-Y 0 1),sq_nonneg (X 0 2-Y 0 2)]
      have h2 : X 0 2=Y 0 2 := by
        nlinarith [sq_nonneg (X 0 0-Y 0 0),sq_nonneg (X 0 1-Y 0 1),sq_nonneg (X 0 2-Y 0 2)]
      apply hne
      ext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact hstable
    simpa [q,spectralQuadratic,hstable] using neg_neg_of_pos hsumpos
  have hqd : ∀ t, 0 ≤ t → HasDerivAt q (dq t) t := by
    intro t ht
    exact (spectralQuadratic_hasDerivAt (fun u => X u-Y u) _ t
      ((hX t ht).sub (hY t ht))).neg
  have hbound : ∀ t, 0 ≤ t → -(12*δ^2) ≤ q t := by
    intro t ht
    have hxn : ‖X t‖ < δ := by simpa using hXt t ht
    have hyn : ‖Y t‖ < δ := by simpa using hYt t ht
    have hdiff := norm_sub_le (X t) (Y t)
    have hn := norm_nonneg (X t-Y t)
    have hlow := negative_spectralQuadratic_lower (X t-Y t)
    dsimp [q]
    nlinarith
  have hdec : ∀ t, 0 ≤ t → dq t ≤ -(κ/2)*N t := by
    intro t ht
    have hh := hpair (X t) (Y t) (hXt t ht) (hYt t ht)
    have heq : saddlePairing ((-spectralGradient) (X t-Y t)) (-f (X t)- -f (Y t))=dq t := by
      change (∑ i, (-(spectralGradient (X t-Y t) i)) * ((-f (X t)- -f (Y t)) i)) =
        -(∑ i, spectralGradient (X t-Y t) i * ((-f (X t)- -f (Y t)) i))
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [heq] at hh
    dsimp [N]
    linarith only [hh]
  exact negative_quadratic_not_globally_bounded q dq N 3 (κ/2) (12*δ^2)
    (by norm_num) (by positivity) (by positivity) hqd
    (fun t _ => sq_nonneg _) (fun t _ => by
      simpa [N,q] using negative_spectralQuadratic_lower (X t-Y t)) hdec hbound hq0

end CoreCouplingGlobal

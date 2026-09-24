import proofs.CompositionalMemory.SemenovPieceEnergy
import proofs.CompositionalMemory.SemenovCheckedSixth
import proofs.CompositionalMemory.SemenovRecoveryParameters

namespace CompositionalMemory.Semenov
open Matrix Polynomial FiniteCopy

theorem checked_piece_combined_drift
    (high : Bool) (zc : Fin 8 → Fin 17 → ℚ) (pc wc : Fin 8 → Fin 8 → Fin 17 → ℚ)
    (A : Fin 8 → Fin 8 → ℚ) (nr : Fin 11 → ℚ) (radius margin : ℚ)
    (hg : MetricGeometryChecks zc pc wc A nr (recoveryEta high) radius margin
      (recoveryL high) (recoveryQ high) (recoveryH high))
    (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (hz : ∀ j,z j=qchebyshevSeries (zc j)) (hP : ∀ i j,P i j=qchebyshevSeries (pc i j))
    (hsym : ∀ i j,P i j=P j i) (scale : ℚ)
    (rb : Fin 8 → Fin 8 → ℚ) (fb : Fin 8 → ℚ)
    (hrow : ∀ i,(∑ j,rb i j) ≤ (1/1000 : ℚ))
    (hfs : (∑ i,fb i^2) ≤ (recoveryForce high)^2)
    (left u : ℝ) (hglobal : left+u ≤ 500)
    (hl : -1 ≤ -1+(scale : ℝ)*u) (hu : -1+(scale : ℝ)*u ≤ 1)
    (hrb : ∀ i j,|aeval (-1+(scale : ℝ)*u) (qpolynomial (metricResidualPolynomial z P scale i j))| ≤ (rb i j : ℝ))
    (hfb : ∀ i,|aeval (-1+(scale : ℝ)*u) (qpolynomial (forceResidualPolynomial z P scale i))| ≤ (fb i : ℝ))
    (hwhite : coefficientMatrix wc (-1+(scale : ℝ)*u)=
      rationalMatrix A*coefficientMatrix pc (-1+(scale : ℝ)*u)*(rationalMatrix A).transpose)
    (hcap : ∀ j,(recoveryVolume : ℝ)*(coordinateUpper zc radius j : ℝ)+1 ≤ (recoveryCountCap : ℝ))
    (s : ReactorState recoveryCountCap recoveryFeedQuota)
    (hunit : pieceCombinedEnergy z P scale recoveryVolume (recoveryEta high)
      ((recoveryVolume : ℝ)*(15231/100000)/2)
      ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) left u s ≤ 1) :
    pieceCombinedSlope z P scale recoveryVolume (recoveryEta high)
      ((recoveryVolume : ℝ)*(15231/100000)/2)
      ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) left u s+
      (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _)).generator
        (pieceCombinedEnergy z P scale recoveryVolume (recoveryEta high)
          ((recoveryVolume : ℝ)*(15231/100000)/2)
          ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) left u) s ≤
      (1/1000000000 : ℝ)+4*((recoveryVolume : ℝ)*(1/500)*(15231/100000))/(recoveryFeedQuota : ℝ)^2 := by
  have hv : (0 : ℝ) < recoveryVolume := by norm_num [recoveryVolume]
  have hK : 0 < recoveryFeedQuota := by norm_num [recoveryFeedQuota]
  have heta : (0 : ℝ) < recoveryEta high := by exact_mod_cast (recovery_parameter_checks high).1
  cases s with
  | none =>
    simp only [pieceCombinedSlope,FiniteJumpModel.generator,nominalReactor,reactorRate,zero_mul,
      Finset.sum_const_zero,zero_add]
    positivity
  | some pair =>
    rcases pair with ⟨n,c⟩
    let t : ℝ := -1+(scale : ℝ)*u
    let nn : Fin 8 → ℕ := fun j => (n j).val
    let nc : Fin 8 → ℝ := fun j => (nn j : ℝ)/(recoveryVolume : ℝ)
    have hp := polynomialMatrix_coefficients pc P hP t
    have hz' := polynomialVector_coefficients zc z hz t
    have hs : ∀ i j,coefficientValue (pc i j) t=coefficientValue (pc j i) t := by
      intro i j
      have hh := congrArg (fun p => aeval t (qpolynomial p)) (hsym i j)
      simpa only [hP,qchebyshevSeries_semantics,coefficientValue] using hh
    have hpos := (geometry_metric_bounds zc pc wc A nr (recoveryEta high) radius margin
      (recoveryL high) (recoveryQ high) (recoveryH high) hg t hl hu hwhite hs
      (nc-(fun j => coefficientValue (zc j) t))).1
    have hD : 0 ≤ pieceQuadratic z P scale recoveryVolume (recoveryEta high) u nn := by
      change 0 ≤ matrixEnergy (polynomialMatrix P t) (nc-polynomialVector z t)/(recoveryEta high : ℝ)
      rw [hp,hz']
      exact div_nonneg hpos heta.le
    have hD6 : (pieceQuadratic z P scale recoveryVolume (recoveryEta high) u nn)^6 ≤ 1 := by
      have hc := centeredInventory_nonneg (recoveryFeedQuota : ℝ)
        ((recoveryVolume : ℝ)*(15231/100000)/2)
        ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) (left+u) c.val
      change (pieceQuadratic z P scale recoveryVolume (recoveryEta high) u nn)^6+_ ≤ 1 at hunit
      linarith only [hunit,hc]
    have hD1 := (pow_le_one_iff_of_nonneg hD (by norm_num : (6 : ℕ) ≠ 0)).mp hD6
    have he : matrixEnergy (polynomialMatrix P t) (nc-polynomialVector z t) ≤ (recoveryEta high : ℝ) :=
      (div_le_one heta).mp hD1
    have he' : matrixEnergy (coefficientMatrix pc t) (nc-(fun j => coefficientValue (zc j) t)) ≤ (recoveryEta high : ℝ) := by
      simpa only [hp,hz'] using he
    have hnc (j : Fin 8) : 0 ≤ nc j := div_nonneg (Nat.cast_nonneg _) hv.le
    have hfirst := checked_polynomial_drift zc pc wc A nr (recoveryEta high) radius margin
      (recoveryL high) (recoveryQ high) (recoveryH high) hg (recovery_parameter_checks high).2.1
      z P hz hP hsym scale (recoveryForce high) rb fb hrow hfs t hl hu hrb hfb hwhite nc
      recoveryVolume hv hnc he
    rw [hp,hz'] at hfirst
    have hroot : (recoveryH high : ℝ)/(recoveryEta high : ℝ) ≤ (recoveryRoot high : ℝ)^2 := by
      exact_mod_cast (recovery_parameter_checks high).2.2.2.1
    have hr : (0 : ℝ) ≤ recoveryRoot high := by exact_mod_cast (recovery_parameter_checks high).2.2.1
    have hsix := checked_sixth_from_quadratic zc pc wc A nr (recoveryEta high) radius margin
      (recoveryL high) (recoveryQ high) (recoveryH high) hg t hl hu hwhite hs
      (polynomialMatrixSlope P scale t) (polynomialVectorSlope z scale t) nc recoveryVolume
      (recoveryForce high) (recoveryRoot high) (1/1000000000) hv hr hnc hroot he' hfirst
      (recovery_scalar_drift_bound high)
    have hchem : 6*(pieceQuadratic z P scale recoveryVolume (recoveryEta high) u nn)^5*
        pieceQuadraticSlope z P scale recoveryVolume (recoveryEta high) u nn+
        (∑ r,reactorRate (recoveryVolume : ℝ) (some (n,c)) r*
          ((pieceQuadratic z P scale recoveryVolume (recoveryEta high) u (rawChannelNext nn r))^6-
           (pieceQuadratic z P scale recoveryVolume (recoveryEta high) u nn)^6)) ≤ (1/1000000000 : ℝ) := by
      dsimp only [pieceQuadratic,pieceQuadraticSlope]
      rw [source_raw_sixth_sum (recoveryVolume : ℝ) (recoveryEta high : ℝ) hv]
      dsimp only [t,nc,nn] at hsix hp hz' ⊢
      simpa only [hp,hz'] using hsix
    have hrad := geometry_tube_radius zc pc wc A nr (recoveryEta high) radius margin
      (recoveryL high) (recoveryQ high) (recoveryH high) hg t hl hu hwhite
      (coefficient_congruence_symmetric pc wc A t hwhite hs) _ he'
    have hcoord (r : Channel) (j : Fin 8) : rawChannelNext nn r j ≤ recoveryCountCap :=
      tube_raw_next_fits zc radius hg.1.2.1.le t hl hu recoveryVolume hv recoveryCountCap nn hrad hcap r j
    exact combined_generator_bound recoveryCountCap recoveryFeedQuota hK recoveryVolume (Nat.cast_nonneg _)
      (fun m => (pieceQuadratic z P scale recoveryVolume (recoveryEta high) u m)^6) (fun _ => by positivity)
      ((recoveryVolume : ℝ)*(15231/100000)/2) (left+u) _ (1/1000000000) n c hcoord
      (feed_mean_below_half_quota (left+u) hglobal) hchem

end CompositionalMemory.Semenov

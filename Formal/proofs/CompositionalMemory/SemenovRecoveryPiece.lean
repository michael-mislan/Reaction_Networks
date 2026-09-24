import proofs.CompositionalMemory.SemenovPieceDrift
import proofs.CompositionalMemory.FiniteRecoveryChain

namespace CompositionalMemory.Semenov
open Matrix Polynomial FiniteCopy Set

/-- One of the fixed polynomial intervals together with its checked data.
This packages the existing leaf certificates for finite-time composition. -/
structure RecoveryPiece (high : Bool) where
  zc : Fin 8 → Fin 17 → ℚ
  pc : Fin 8 → Fin 8 → Fin 17 → ℚ
  wc : Fin 8 → Fin 8 → Fin 17 → ℚ
  A : Fin 8 → Fin 8 → ℚ
  nr : Fin 11 → ℚ
  radius : ℚ
  margin : ℚ
  z : Fin 8 → QCoefficients
  P : Fin 8 → Fin 8 → QCoefficients
  scale : ℚ
  left : ℚ
  right : ℚ
  zLeft : Fin 8 → ℚ
  zRight : Fin 8 → ℚ
  pLeft : Fin 8 → Fin 8 → ℚ
  pRight : Fin 8 → Fin 8 → ℚ
  rb : Fin 8 → Fin 8 → ℚ
  fb : Fin 8 → ℚ
  geometry : MetricGeometryChecks zc pc wc A nr (recoveryEta high) radius margin
    (recoveryL high) (recoveryQ high) (recoveryH high)
  cache_z : ∀ j,z j=qchebyshevSeries (zc j)
  cache_P : ∀ i j,P i j=qchebyshevSeries (pc i j)
  symmetry : ∀ i j,P i j=P j i
  z_endpoints : ∀ j,qeval (-1) (z j)=zLeft j ∧ qeval 1 (z j)=zRight j
  p_endpoints : ∀ i j,qeval (-1) (P i j)=pLeft i j ∧ qeval 1 (P i j)=pRight i j
  timing : 0 ≤ left ∧ left<right ∧ right≤500 ∧ scale=2/(right-left)
  residual_rows : ∀ i,(∑ j,rb i j) ≤ (1/1000 : ℚ)
  force_squares : (∑ i,fb i^2) ≤ (recoveryForce high)^2
  residual : ∀ t : ℝ,-1 ≤ t → t ≤ 1 → ∀ i j,
    |aeval t (qpolynomial (metricResidualPolynomial z P scale i j))| ≤ (rb i j : ℝ)
  force : ∀ t : ℝ,-1 ≤ t → t ≤ 1 → ∀ i,
    |aeval t (qpolynomial (forceResidualPolynomial z P scale i))| ≤ (fb i : ℝ)
  whitened : ∀ t : ℝ,coefficientMatrix wc t=rationalMatrix A*coefficientMatrix pc t*(rationalMatrix A).transpose
  capacity : ∀ j,(recoveryVolume : ℚ)*coordinateUpper zc radius j+1 ≤ (recoveryCountCap : ℚ)

namespace RecoveryPiece
variable {high : Bool}

noncomputable def duration (p : RecoveryPiece high) : NNReal :=
  ⟨((p.right-p.left : ℚ) : ℝ),by exact_mod_cast sub_nonneg.mpr p.timing.2.1.le⟩

noncomputable def energy (p : RecoveryPiece high) (u : ℝ) :
    ReactorState recoveryCountCap recoveryFeedQuota → ℝ :=
  pieceCombinedEnergy p.z p.P p.scale recoveryVolume (recoveryEta high)
    ((recoveryVolume : ℝ)*(15231/100000)/2)
    ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) p.left u

noncomputable def slope (p : RecoveryPiece high) (u : ℝ) :
    ReactorState recoveryCountCap recoveryFeedQuota → ℝ :=
  pieceCombinedSlope p.z p.P p.scale recoveryVolume (recoveryEta high)
    ((recoveryVolume : ℝ)*(15231/100000)/2)
    ((recoveryVolume : ℝ)*(1/500)*(15231/100000)) p.left u

noncomputable def driftCost : ℝ := (1/1000000000 : ℝ)+
  4*((recoveryVolume : ℝ)*(1/500)*(15231/100000))/(recoveryFeedQuota : ℝ)^2

theorem energy_nonneg (p : RecoveryPiece high) (u : ℝ) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    0 ≤ p.energy u s := by
  unfold energy pieceCombinedEnergy
  exact reactor_combined_energy_nonneg _ (fun _ => by positivity) _ _ _ s

theorem energy_derivative (p : RecoveryPiece high) (u : ℝ) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    HasDerivAt (fun t => p.energy t s) (p.slope u s) u :=
  piece_combined_derivative p.z p.P p.symmetry p.scale _ _ _ _ _ u s

theorem local_drift (p : RecoveryPiece high) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) p.duration)
    (s : ReactorState recoveryCountCap recoveryFeedQuota) (hs : p.energy u s ≤ 1) :
    p.slope u s+
      (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _)).generator
        (p.energy u) s ≤ driftCost := by
  have hd : 0 < (p.duration : ℝ) := by
    change (0 : ℝ) < ((p.right-p.left : ℚ) : ℝ)
    exact_mod_cast sub_pos.mpr p.timing.2.1
  have ht := normalized_time_mem p.duration (p.scale : ℝ) u hd
    (by change (p.scale : ℝ)=2/((p.right-p.left : ℚ) : ℝ); exact_mod_cast p.timing.2.2.2) hu
  have hglobal : (p.left : ℝ)+u ≤ 500 := by
    have hr : (p.right : ℝ) ≤ 500 := by exact_mod_cast p.timing.2.2.1
    have hu' := hu.2
    change u ≤ ((p.right-p.left : ℚ) : ℝ) at hu'
    rw [Rat.cast_sub] at hu'
    linarith only [hr,hu']
  exact checked_piece_combined_drift high p.zc p.pc p.wc p.A p.nr p.radius p.margin p.geometry
    p.z p.P p.cache_z p.cache_P p.symmetry p.scale p.rb p.fb p.residual_rows p.force_squares
    p.left u hglobal ht.1 ht.2 (p.residual _ ht.1 ht.2) (p.force _ ht.1 ht.2) (p.whitened _)
    (fun j => by exact_mod_cast p.capacity j) s hs

theorem recovery_bound (p : RecoveryPiece high) (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      p.duration (fun y => smoothQuadraticCap (p.energy p.duration y)) s ≤
      smoothQuadraticCap (p.energy 0 s)+2*(p.duration : ℝ)*driftCost := by
  exact finite_smooth_recovery_bound _ p.duration p.energy p.slope driftCost
    (by unfold driftCost; positivity) (fun u _ y => p.energy_nonneg u y)
    (fun u _ y => p.energy_derivative u y) (fun u hu y hy => p.local_drift u hu y hy)
    _ (fun _ => le_rfl) s

end RecoveryPiece
end CompositionalMemory.Semenov

import proofs.CompositionalMemory.SemenovRecoveryEndpoints

namespace CompositionalMemory.Semenov
open FiniteCopy

noncomputable def leftObservable {high : Bool} (p : RecoveryPiece high) :
    ReactorState recoveryCountCap recoveryFeedQuota → ℝ :=
  fun s => smoothQuadraticCap (boundaryEnergy high p.zLeft p.pLeft p.left s)

noncomputable def rightObservable {high : Bool} (p : RecoveryPiece high) :
    ReactorState recoveryCountCap recoveryFeedQuota → ℝ :=
  fun s => smoothQuadraticCap (boundaryEnergy high p.zRight p.pRight p.right s)

noncomputable def seriesObservable {high : Bool} (p : ℕ → RecoveryPiece high) :
    ℕ → ReactorState recoveryCountCap recoveryFeedQuota → ℝ
  | 0 => leftObservable (p 0)
  | i+1 => rightObservable (p i)

theorem recovery_series_bound {high : Bool} (p : ℕ → RecoveryPiece high) (n : ℕ)
    (hj : ∀ i,i+1<n → (p i).right=(p (i+1)).left ∧
      (p i).zRight=(p (i+1)).zLeft ∧ (p i).pRight=(p (i+1)).pLeft)
    (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      (∑ i ∈ Finset.range n,(p i).duration) (seriesObservable p n) s ≤
      leftObservable (p 0) s+∑ i ∈ Finset.range n,2*((p i).duration : ℝ)*RecoveryPiece.driftCost := by
  apply finite_recovery_chain _ (fun i => (p i).duration) (seriesObservable p)
    (fun i => 2*((p i).duration : ℝ)*RecoveryPiece.driftCost) n ?_ s
  intro i hi y
  cases i with
  | zero => exact (p 0).boundary_recovery_bound y
  | succ i =>
    obtain ⟨ht,hz,hP⟩ := hj i hi
    have he : rightObservable (p i)=leftObservable (p (i+1)) := by
      unfold rightObservable leftObservable
      rw [ht,hz,hP]
    have hh := (p (i+1)).boundary_recovery_bound y
    change finiteTimeExpectation _ _ (rightObservable (p (i+1))) y ≤
      rightObservable (p i) y+2*((p (i+1)).duration : ℝ)*RecoveryPiece.driftCost
    rw [he]
    exact hh

theorem recovery_series_total_bound {high : Bool} (p : ℕ → RecoveryPiece high) (n : ℕ)
    (hj : ∀ i,i+1<n → (p i).right=(p (i+1)).left ∧
      (p i).zRight=(p (i+1)).zLeft ∧ (p i).pRight=(p (i+1)).pLeft)
    (T : NNReal) (ht : (∑ i ∈ Finset.range n,(p i).duration)=T)
    (s : ReactorState recoveryCountCap recoveryFeedQuota) :
    finiteTimeExpectation (nominalReactor recoveryCountCap recoveryFeedQuota recoveryVolume (Nat.cast_nonneg _))
      T (seriesObservable p n) s ≤
      leftObservable (p 0) s+2*(T : ℝ)*RecoveryPiece.driftCost := by
  have hh := recovery_series_bound p n hj s
  rw [ht] at hh
  have hc : (∑ i ∈ Finset.range n,2*((p i).duration : ℝ)*RecoveryPiece.driftCost)=
      2*(T : ℝ)*RecoveryPiece.driftCost := by
    rw [← Finset.sum_mul,← Finset.mul_sum]
    have hs : (∑ i ∈ Finset.range n,((p i).duration : ℝ))=(T : ℝ) := by exact_mod_cast ht
    rw [hs]
  rw [hc] at hh
  exact hh

end CompositionalMemory.Semenov

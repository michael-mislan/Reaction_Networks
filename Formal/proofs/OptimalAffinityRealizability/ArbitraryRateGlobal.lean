import proofs.OptimalAffinityRealizability.GlobalEquality

namespace OptimalAffinityRealizability
noncomputable section

def actualLogForward {n : ℕ} (source : SquareSource n) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  source.forwardRate i * Real.exp (source.reactant.transpose.mulVec z i)

def actualLogReverse {n : ℕ} (source : SquareSource n) (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  source.reverseRate i * Real.exp (source.product.transpose.mulVec z i)

def actualLogCurrent {n : ℕ} (source : SquareSource n) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => actualLogForward source z i - actualLogReverse source z i

def actualLogFlux {n : ℕ} (source : SquareSource n) (z : Fin n → ℝ) : ℝ :=
  source.netStoich.mulVec (actualLogCurrent source z) source.controlled

def ActualStationary {n : ℕ} (source : SquareSource n) (z : Fin n → ℝ) : Prop :=
  ∀ i, i ≠ source.controlled → source.netStoich.mulVec (actualLogCurrent source z) i = 0

theorem actualLogCurrent_at_reference {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q z₀ z : Fin n → ℝ)
    (hq : ∀ i, 1 < q i)
    (hnet : ∀ i, actualLogCurrent source z₀ i = J * g i)
    (hratio : ∀ i, actualLogForward source z₀ i = q i * actualLogReverse source z₀ i) :
    actualLogCurrent source z = reconstructedLogReactionCurrent source J g q (z-z₀) := by
  funext i
  have hn := hnet i
  have hr := hratio i
  change actualLogForward source z₀ i - actualLogReverse source z₀ i = J * g i at hn
  have hm : actualLogReverse source z₀ i = J * g i / (q i-1) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr (hq i)))).mpr
    nlinarith
  have hp : actualLogForward source z₀ i = J * g i * q i / (q i-1) := by
    rw [hr, hm]
    ring
  have hforward : actualLogForward source z i = actualLogForward source z₀ i *
      Real.exp (source.reactant.transpose.mulVec (z-z₀) i) := by
    unfold actualLogForward
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    simp [Matrix.mulVec_sub]
  have hreverse : actualLogReverse source z i = actualLogReverse source z₀ i *
      Real.exp (source.product.transpose.mulVec (z-z₀) i) := by
    unfold actualLogReverse
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    simp [Matrix.mulVec_sub]
  change actualLogForward source z i - actualLogReverse source z i = _
  rw [hforward, hreverse, hp, hm]
  rfl

/-- Arbitrary positive rates and arbitrary reference state: derivative balance
is represented by the actual one-way flux ratio and the common response data.
No assumption of local or global domination is used. -/
theorem arbitraryRateSource_globalMaximum {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (g f q z₀ : Fin n → ℝ)
    (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 1 < q i)
    (hr : ∀ i, (responseMatrix source).transpose.mulVec f i = q i * f i)
    (hz₀ : ActualStationary source z₀) (hJ : 0 < actualLogFlux source z₀)
    (hratio : ∀ i, actualLogForward source z₀ i = q i * actualLogReverse source z₀ i)
    (z : Fin n → ℝ) (hz : ActualStationary source z) :
    actualLogFlux source z ≤ actualLogFlux source z₀ := by
  have hnet := current_eq_controlledProductionRay source g (actualLogCurrent source z₀) hmode hz₀
  have hid := actualLogCurrent_at_reference source (actualLogFlux source z₀) g q z₀ z hq
    (fun i => congrFun hnet i) hratio
  have hstation : GlobalStationaryFiber source (actualLogFlux source z₀) g q (z-z₀) := by
    intro i hi
    change source.netStoich.mulVec (reconstructedLogReactionCurrent source _ g q (z-z₀)) i = 0
    rw [← hid]
    exact hz i hi
  have hb := reconstructedSource_globalMaximum source (actualLogFlux source z₀) g f q
    hJ hg hmode hT hf hq hr (z-z₀) hstation
  change source.netStoich.mulVec (reconstructedLogReactionCurrent source _ g q (z-z₀))
    source.controlled ≤ _ at hb
  rw [← hid] at hb
  exact hb

end
end OptimalAffinityRealizability

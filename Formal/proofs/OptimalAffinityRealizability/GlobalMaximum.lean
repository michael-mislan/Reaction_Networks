import proofs.OptimalAffinityRealizability.GlobalNormalization

namespace OptimalAffinityRealizability
noncomputable section

/-- A uniform bound on the entire positive stationary fiber, represented by
all real log-concentration states. Global domination is a conclusion. -/
theorem reconstructedSource_globalMaximum {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g f q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hmode : ControlledProductionMode source g)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 1 < q i)
    (hr : ∀ i, (responseMatrix source).transpose.mulVec f i = q i * f i)
    (z : Fin n → ℝ) (hz : GlobalStationaryFiber source J g q z) :
    controlledFluxAtLogState source J g q z ≤ J := by
  have hb := commonResponseCurrent_le_one (responseMatrix source) f q
    (source.reactant.transpose.mulVec z)
    (controlledFluxAtLogState source J g q z / J) hT hf hq hr
    (stationary_commonResponseCurrent source J g q z hJ hg hmode hz)
  exact (div_le_one hJ).mp hb

end
end OptimalAffinityRealizability

import proofs.OptimalAffinityRealizability.GlobalCapacity

namespace OptimalAffinityRealizability
noncomputable section

theorem rawSquareSource_globalNearCapacity {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f, GlobalRealizable source J g f ∧
      responseLayerCapacity (responseMatrix source) weights ≤
        responseObjective (responseMatrix source) weights f ∧
      responseObjective (responseMatrix source) weights f <
        responseLayerCapacity (responseMatrix source) weights + ε := by
  let V := realizationValueSet (responseMatrix source) weights
    (ResponseFeasible (responseMatrix source))
  have hV : V.Nonempty := by
    obtain ⟨f, hf⟩ := hne
    exact ⟨_, f, hf, rfl⟩
  have hb : BddBelow V := OptimalAffinityCorrected.responseValueSet_bddBelow _ _
  obtain ⟨v, hv, hlt⟩ := exists_lt_of_csInf_lt hV
    (show sInf V < sInf V + ε by linarith)
  have hgV : v ∈ realizationValueSet (responseMatrix source) weights
      (GlobalRealizable source J g) := by
    rw [rawSquareSource_globalValueSetEquality source weights J g hclass hT hJ hg hmode]
    exact hv
  obtain ⟨f, hf, rfl⟩ := hgV
  exact ⟨f, hf, csInf_le hb hv, hlt⟩

theorem rawSquareSource_uniqueGlobalCapacityEquality {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (weights : Fin n → ℕ) (J : ℝ) (g : Fin n → ℝ)
    (hclass : AccessibleRootedResponseClass source)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hconn : ResponseStronglyConnected (responseMatrix source))
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hmode : ControlledProductionMode source g)
    (hne : ∃ f, ResponseFeasible (responseMatrix source) f) :
    (∃ f, UniqueGlobalRealizable source J g f) ∧
    realizationCapacity (responseMatrix source) weights (UniqueGlobalRealizable source J g) =
      responseLayerCapacity (responseMatrix source) weights := by
  constructor
  · obtain ⟨f, hf⟩ := hne
    obtain ⟨f', _, hw⟩ := accessibleRootedResponseClass_rayStrictLocal source J g
      hclass hJ hg hmode f hf
    exact ⟨f', strictLocal_uniqueGlobalRealizable source J g f' hT hconn hw⟩
  · unfold realizationCapacity responseLayerCapacity
    rw [rawSquareSource_uniqueGlobalValueSetEquality source weights J g hclass hT hconn hJ hg hmode]
    rfl

end
end OptimalAffinityRealizability

import proofs.OptimalAffinityCorrected.SourceAdapter
import proofs.OptimalAffinityCorrected.RecyclingFamilyGlobal
import proofs.OptimalAffinityCorrected.ZeroDiagonalCircuit

namespace OptimalAffinityCorrected

noncomputable section

def SourceClosurePackage : Prop :=
  (∀ (n : ℕ) (P : ResponseOptimalPoint n),
      ∃ f, ForwardResponse P.T f ∧
        P.expAffinity = responseObjective P.T P.g f) ∧
  (∀ (n : ℕ) (P : ResponseOptimalPoint n),
      responseProfileBound P.T P.g ≤ P.expAffinity) ∧
  (∀ (n : ℕ) (T : Fin n → Fin n → ℝ) (g : Fin n → ℕ),
      (responseValueSet T g).Nonempty →
      IsGLB (responseValueSet T g) (responseProfileBound T g)) ∧
  (CircuitSourceValid ∧
      (∀ i, circuitT i i = 0) ∧
      CircuitUniqueGlobalMaximum 1 1 1 ∧
      circuitExpAffinity 1 1 1 = 9 / 5 ∧
      circuitGrossRatio = 2 ∧
      circuitExpAffinity 1 1 1 < circuitGrossRatio) ∧
  (∀ m : ℕ, 2 ≤ m → IntegerRecyclingSourceCertificate m) ∧
  (∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, IntegerRecyclingSourceCertificate m ∧
        let r := 1 + 1 / (m : ℝ)
        1 < recyclingFamilyExpAffinity (m : ℝ) r ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 1 + ε ∧
        recyclingFamilyExpAffinity (m : ℝ) r < 2)

theorem sourceClosurePackage : SourceClosurePackage := by
  refine ⟨?_, ?_, ?_, zeroDiagonalSourceCounterexample, ?_,
    noUniformPositiveSourceAffinityGap⟩
  · intro n P
    exact source_to_response_adapter P
  · intro n P
    exact source_response_lower_bound P
  · intro n T g hne
    exact responseProfileBound_isGLB T g hne
  · intro m hm
    exact integerRecyclingSourceCertificate m hm

end
end OptimalAffinityCorrected

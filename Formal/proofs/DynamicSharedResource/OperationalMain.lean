import proofs.DynamicSharedResource.OperationalAccounts
import proofs.DynamicSharedResource.SourcePerturbation

namespace DynamicSharedResource.Certificate
noncomputable section
open MeasureTheory

/-- Nominal operational certificate, with no assumed capture or stability. -/
theorem fast_joint_service :
    (0:ℝ) < enlargedEpsilon ∧
    Metric.ball preparation enlargedEpsilon ⊆ {u | EnlargedPrepared u} ∧
    (∀ u₀, EnlargedPrepared u₀ → Physical u₀ ∧ HT u₀<4 ∧ InRect recoveryR (coordinates u₀)) ∧
    (∀ u₀ : State, InRect recoveryR (coordinates u₀) → ∃ u : ℝ → State,
      u 0=u₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt u (nominal (u t)) t) ∧
      (∀ v : ℝ → State, v 0=u₀ →
        (∀ t, 0 ≤ t → HasDerivAt v (nominal (v t)) t) → ∀ t, 0 ≤ t → v t=u t) ∧
      (∀ t, 0 ≤ t → Physical (u t) ∧ InRect recoveryR (coordinates (u t)) ∧
        (207/20:ℝ) ≤ HG (u t) ∧ (391/100:ℝ) ≤ HT (u t)) ∧
      (∀ t, 1/250 ≤ t → InRect serviceR (coordinates (u t)) ∧ (401/100:ℝ) ≤ HT (u t)) ∧
      (∀ T, 0 ≤ T → (∫ t in 0..T, max (10-HG (u t)) 0)=0 ∧
        (∫ t in 0..T, max (4-HT (u t)) 0) ≤ (9/25000:ℝ)) ∧
      (∀ a T, 1/250 ≤ a → 0 ≤ T →
        (207/20)*T ≤ ∫ t in a..(a+T), HG (u t) ∧
        (401/100)*T ≤ ∫ t in a..(a+T), HT (u t)) ∧
      (∀ a T, 1/250 ≤ a → 0 ≤ T →
        (359/25)*T-1/10 ≤ ∫ t in a..(a+T), regen (3/25) (u t 0))) := by
  refine ⟨by norm_num [enlargedEpsilon],enlarged_contains_ball,?_,?_⟩
  · intro u₀ h₀
    exact ⟨enlarged_prepared_physical u₀ h₀,enlarged_prepared_deficient u₀ h₀,
      enlarged_prepared_in_recovery u₀ h₀⟩
  · intro u₀ h₀
    obtain ⟨u,hzero,hu,hunique,hrec,hserv⟩ := operational_recovery u₀ h₀
    have hp : InRect recoveryR (coordinates (u 0)) := by simpa only [hzero] using h₀
    exact ⟨u,hzero,hu,hunique,hrec,hserv,operational_shortfall u hp hu,
      operational_windows u hp hu,regeneration_expenditure u hp hu⟩

end
end DynamicSharedResource.Certificate

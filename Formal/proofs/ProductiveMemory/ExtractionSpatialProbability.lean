import proofs.ProductiveMemory.ExtractionSpatialBoundary

namespace ProductiveMemory
open FiniteCopy HeritableCompositions ResourceLimitedCompetition Set
open scoped NNReal
noncomputable section
set_option Elab.async false

local instance productiveProbabilityDecidableEq (D : Finset ProductiveState) : DecidableEq (ProductiveStopped D) :=
  Classical.decEq _

theorem productive_spatial_generator (N M W0 J : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (x : ProductiveStopped (productiveActiveDomain N M W0 J rho zL zH)) :
    (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).generator
      (productiveSpatialObservable N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH)) x ≤
      16*(M:ℝ)*((N:ℝ)*localAlpha*readyLevel/960)*Real.exp ((N:ℝ)*localAlpha*readyLevel/2) := by
  classical
  cases x with
  | inr e =>
    rw [productive_terminal_generator]
    unfold localAlpha readyLevel outerLevel
    positivity
  | inl s =>
    have h := productive_potential_generator_le rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)
      (productiveSpatialObservable N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
      s (extractionCellSpatial N rho zL zH) rfl
      (productive_spatial_next_le_raw N W0 J hlarge rho zL zH _ s)
    have hb := productive_raw_spatial_bound N M W0 J hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax s
    rw [productive_raw_generator_sum] at hb
    have hh := h.trans hb
    convert hh using 1
    ring

def productiveDivisionFailure (N W0 J : ℕ) (rho zL zH : ℝ) (D : Finset ProductiveState) :
    Set (ProductiveStopped D) :=
  {x | ∃ e, x=.inr e ∧ productiveReason N W0 J rho zL zH e=.divisionEnergy}

theorem productive_division_failure_bound (N M W0 J : ℕ) (hN : 1 ≤ N)
    (hlarge : (200000000000000000000:ℝ) ≤ N) (rho zL zH γ : ℝ)
    (hr : rho ∈ Icc (9999/1000000:ℝ) (1/100))
    (hzL : zL ∈ Icc (98172/100000:ℝ) (98174/100000))
    (hzH : zH ∈ Icc (289014/100000:ℝ) (289017/100000))
    (hsL : extractDrift rho 0 (lift rho zL) = 0) (hsH : extractDrift rho 0 (lift rho zH) = 0)
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 1/100000000000)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ x, (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
      (productiveActiveDomain N M W0 J rho zL zH)).total x ≤ q)
    (s : ProductiveActive (productiveActiveDomain N M W0 J rho zL zH)) :
    Real.exp (2*(N:ℝ)*localAlpha*readyLevel)*
      ((productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
        (productiveActiveDomain N M W0 J rho zL zH)).uniformize q hq hclock).poissonized (q*t)
        (FiniteKernel.eventIndicator (productiveDivisionFailure N W0 J rho zL zH
          (productiveActiveDomain N M W0 J rho zL zH))) (.inl s) ≤
      potentialSum (extractionCellSpatial N rho zL zH) s.val.population+
        (t:ℝ)*(16*(M:ℝ)*((N:ℝ)*localAlpha*readyLevel/960)*Real.exp ((N:ℝ)*localAlpha*readyLevel/2)) := by
  classical
  apply (productiveStoppedModel rho γ (by linarith [hr.1]) hγ (4*W0) N W0 J zL zH
    (productiveActiveDomain N M W0 J rho zL zH)).uniformized_event_bound q t hq hclock
      (productiveDivisionFailure N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
      (productiveSpatialObservable N W0 J rho zL zH (productiveActiveDomain N M W0 J rho zL zH))
  · exact productive_spatial_nonneg N W0 J rho zL zH _
  · rintro x ⟨e,rfl,he⟩
    simp [productiveSpatialObservable,he]
  · exact productive_spatial_generator N M W0 J hN hlarge rho zL zH γ hr hzL hzH hsL hsH hγ hγmax

end
end ProductiveMemory

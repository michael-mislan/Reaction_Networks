import proofs.CompositionalMemory.SourceScaling
import proofs.CompositionalMemory.WordChronologicalGeneration

namespace CompositionalMemory
open FiniteCopy HeritableCompositions RandomViability MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- The constructed source is nonexplosive and its actual two-phase trajectory payoff
is identified with the same normalized kernel satisfying both molecular scaling bounds. -/
theorem source_actual_word_scaling {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (hlarge : scalingCopyFloor ≤ N) (γ κ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (σ : Fin k → Bool) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ) :
    Nonempty (WordBirthCount N (sourceWordCenter σ) σ) ∧
    (∀ s : ModularCountState k, ∀ᵐ z ∂frozenCountTrajectory γ w hγ.le hw N s,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop) ∧
    ∃ (hN : 1 ≤ N) (K : WordBirthCount N (sourceWordCenter σ) σ →
        FiniteLaw (WordBirthOutcome N (sourceWordCenter σ) σ)),
      (∀ (H : WordBirthOutcome N (sourceWordCenter σ) σ → ℝ), H none=0 →
        (∀ x,0 ≤ H x ∧ H x ≤ 1) → ∀ n,
          wordPhysicalGeneration hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ) σ H n=
            ENNReal.ofReal ((K n).expect H)) ∧
      (∀ (G : ℕ) n,
        1-(G : ℝ)*((k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent)) ≤ wordLineageSuccess K G n ∧
        wordLineageSuccess K G n ≤ (1-(1/2 : ℝ)^(280*N))^(k*G)) ∧
      (∀ (G : ℕ), 1 ≤ G → ∀ η : ℝ, 0 < η → η < 1 → ∀ n,
        (Real.log ((G : ℝ)*((k : ℝ)*scalingPrefactor γ)/η)/scalingExponent ≤ N →
          1-η ≤ wordLineageSuccess K G n) ∧
        (1-η ≤ wordLineageSuccess K G n →
          Real.log (((k*G : ℕ) : ℝ)/(-Real.log (1-η)))/(280*Real.log 2) ≤ N)) := by
  obtain ⟨hN,q₀,q₁,hq₀,hq₁,hc₀,hc₁,hupper⟩ :=
    source_generation_clocks hk N hlarge γ κ hγ hγmax hκ hκmax σ w hdiag hsym hw hrow
  let K := wordGenerationLaw hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ)
    σ q₀ q₁ hq₀ hq₁ hc₀ hc₁
  have hlower := source_generation_failure_lower hk γ hγ w hw N hN σ q₀ q₁ hq₀ hq₁ hc₀ hc₁
  have hsurv (G : ℕ) (n) : wordLineageSuccess K G n ≤ (1-(1/2 : ℝ)^(280*N))^(k*G) := by
    have h := word_lineage_upper K (necessitySurvival k N) (necessitySurvival_nonneg k N) hlower G n
    simpa only [necessitySurvival,← pow_mul] using h
  refine ⟨source_word_birth_nonempty N hlarge σ,
    frozen_count_nonexplosive hk γ w hγ.le hw N,hN,K,?_,?_,?_⟩
  · intro H hH0 hH n
    exact word_physical_generation_eq hk γ hγ w hw N hN (sourceWordCenter σ)
      (sourceWordCenter_upper σ) σ q₀ q₁ hq₀ hq₁ hc₀ hc₁ H hH0 hH n
  · intro G n
    exact ⟨word_lineage_bound K _ (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg k) (scalingPrefactor_pos γ hγ).le) (Real.exp_pos _).le) hupper G n,
      hsurv G n⟩
  · intro G hG η hη hη1 n
    constructor
    · intro hb
      exact word_lineage_copy_tradeoff K k N G hk hG γ η hγ hη hupper hb n
    · intro hs
      exact necessary_copy_budget N (k*G) (Nat.mul_pos (by omega) (by omega)) η hη hη1 (hs.trans (hsurv G n))

end CompositionalMemory

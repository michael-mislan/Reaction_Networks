import proofs.CompositionalMemory.WordLineage

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

theorem word_lineage_copy_tradeoff {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (k N G : ℕ) (hk : 1 ≤ k) (hG : 1 ≤ G)
    (γ η : ℝ) (hγ : 0 < γ) (hη : 0 < η)
    (hK : ∀ n, (K n).mass none ≤ (k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent))
    (hbudget : Real.log ((G : ℝ)*((k : ℝ)*scalingPrefactor γ)/η)/scalingExponent ≤ N)
    (n : α) : 1-η ≤ wordLineageSuccess K G n := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hGr : (0 : ℝ) < G := by exact_mod_cast (by omega : 0 < G)
  have he := exponential_budget_le ((G : ℝ)*((k : ℝ)*scalingPrefactor γ))
    scalingExponent N η (mul_pos hGr (mul_pos hkr (scalingPrefactor_pos γ hγ)))
    scalingExponent_pos hη hbudget
  have h := word_lineage_bound K _ (mul_nonneg
    (mul_nonneg hkr.le (scalingPrefactor_pos γ hγ).le) (Real.exp_pos _).le) hK G n
  nlinarith only [he,h]

/-- Existence of the literal constructed source generation kernel, with uniform
one-step and designated-lineage estimates. Its witness is wordGenerationLaw. -/
theorem source_word_lineage {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (hlarge : scalingCopyFloor ≤ N) (γ κ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (σ : Fin k → Bool) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ) :
    Nonempty (WordBirthCount N (sourceWordCenter σ) σ) ∧
    ∃ K : WordBirthCount N (sourceWordCenter σ) σ →
        FiniteLaw (WordBirthOutcome N (sourceWordCenter σ) σ),
      (∀ n, (K n).mass none ≤ (k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent)) ∧
      (∀ (G : ℕ) n, 1-(G : ℝ)*((k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent)) ≤
        wordLineageSuccess K G n) ∧
      (∀ G : ℕ, 1 ≤ G → ∀ η : ℝ, 0 < η →
        Real.log ((G : ℝ)*((k : ℝ)*scalingPrefactor γ)/η)/scalingExponent ≤ N →
        ∀ n, 1-η ≤ wordLineageSuccess K G n) := by
  obtain ⟨hN,q₀,q₁,hq₀,hq₁,hc₀,hc₁,hbound⟩ :=
    source_generation_clocks hk N hlarge γ κ hγ hγmax hκ hκmax σ w hdiag hsym hw hrow
  refine ⟨source_word_birth_nonempty N hlarge σ,
    wordGenerationLaw hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ)
      σ q₀ q₁ hq₀ hq₁ hc₀ hc₁,hbound,?_,?_⟩
  · intro G n
    exact word_lineage_bound _ _ (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg k) (scalingPrefactor_pos γ hγ).le) (Real.exp_pos _).le)
      hbound G n
  · intro G hG η hη hb n
    exact word_lineage_copy_tradeoff _ k N G hk hG γ η hγ hη hbound hb n

end CompositionalMemory

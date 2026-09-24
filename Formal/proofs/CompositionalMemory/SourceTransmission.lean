import proofs.CompositionalMemory.WordGenerationBound

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC HeritableCompositions Set

noncomputable def sourceWordLow : ℝ := Classical.choose low_source_root
noncomputable def sourceWordHigh : ℝ := Classical.choose high_source_root

theorem sourceWordLow_spec :
    sourceWordLow ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000) ∧
      Stationary sourceRates (lift sourceRates sourceWordLow) := Classical.choose_spec low_source_root

theorem sourceWordHigh_spec :
    sourceWordHigh ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000) ∧
      Stationary sourceRates (lift sourceRates sourceWordHigh) := Classical.choose_spec high_source_root

noncomputable def sourceWordCenter {k : ℕ} (σ : Fin k → Bool) : Fin k → Point :=
  wordCenter sourceWordLow sourceWordHigh σ

theorem sourceWordCenter_upper {k : ℕ} (σ : Fin k → Bool) :
    ∀ i a, sourceWordCenter σ i a ≤ 34 :=
  (word_center_bounds sourceWordLow sourceWordHigh σ sourceWordLow_spec.1 sourceWordHigh_spec.1).1

noncomputable def scalingExponent : ℝ := localAlpha*innerEnergy/2
noncomputable def scalingPrefactor (γ : ℝ) : ℝ := 2703+11/(5*γ)
def scalingCopyFloor : ℕ := 140000000000000000000

theorem scalingExponent_pos : 0 < scalingExponent := by
  norm_num [scalingExponent,localAlpha,innerEnergy,outerEnergy]

theorem scalingPrefactor_pos (γ : ℝ) (hγ : 0 < γ) : 0 < scalingPrefactor γ := by
  unfold scalingPrefactor
  positivity

/-- Constructive source transmission bound. Clocks exist for the literal finite
two-phase law; no inheritance or offspring-error hypothesis is supplied. -/
theorem source_generation_clocks {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (hlarge : scalingCopyFloor ≤ N) (γ κ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (σ : Fin k → Bool) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ) :
    ∃ (hN : 1 ≤ N) (q₀ q₁ : NNReal) (hq₀ : 0 < (q₀ : ℝ)) (hq₁ : 0 < (q₁ : ℝ))
      (hc₀ : ∀ x, (retainedModularModel γ w hγ.le hw N
        (productDomain N (sourceWordCenter σ) (wordEnergy σ) outerEnergy)).total x ≤ q₀)
      (hc₁ : ∀ x, (retainedModularModel γ w hγ.le hw N
        (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))).total x ≤ q₁),
      ∀ n : WordBirthCount N (sourceWordCenter σ) σ,
        (wordGenerationLaw hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ)
          σ q₀ q₁ hq₀ hq₁ hc₀ hc₁ n).mass none ≤
          (k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent) := by
  classical
  have hN : 1 ≤ N := by unfold scalingCopyFloor at hlarge; omega
  let M₀ := retainedModularModel γ w hγ.le hw N (productDomain N (sourceWordCenter σ) (wordEnergy σ) outerEnergy)
  let M₁ := retainedModularModel γ w hγ.le hw N (productDomain N (sourceWordCenter σ) (wordEnergy σ) (2*innerEnergy))
  obtain ⟨q₀,hq₀,hd₀,hc₀⟩ := M₀.exists_clock ((N : ℝ)*localAlpha*innerEnergy/672)
  obtain ⟨q₁,hq₁,hd₁,hc₁⟩ := M₁.exists_clock (19*(γ/2)*((k*N : ℕ) : ℝ)/400)
  refine ⟨hN,q₀,q₁,hq₀,hq₁,hc₀,hc₁,?_⟩
  intro n
  have h := word_generation_failure hk N hN hlarge sourceWordLow sourceWordHigh γ κ σ
    sourceWordLow_spec.1 sourceWordHigh_spec.1 sourceWordLow_spec.2 sourceWordHigh_spec.2
    w hdiag hsym hw hrow hγ hγmax hκ hκmax q₀ q₁ hq₀ hq₁ hc₀ hc₁ hd₀ hd₁ n
  have he : -(N : ℝ)*scalingExponent = -(N : ℝ)*localAlpha*innerEnergy/2 := by
    unfold scalingExponent
    ring
  simpa only [scalingPrefactor,he] using h

end CompositionalMemory

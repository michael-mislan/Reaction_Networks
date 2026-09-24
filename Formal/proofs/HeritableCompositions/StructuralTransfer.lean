import proofs.HeritableCompositions.SourceBirthGeometry

namespace HeritableCompositions
open FiniteCopy

/-- Quantitative inheritance for the literal source, consumptive membrane growth,
and complementary partition, transferred from algebraic generator certificates. -/
structure HeredityConclusion {γ : ℝ} (C : GrowthCertificate γ)
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) : Prop where
  exponent_positive : 0 < heredityExponent
  prefactor_positive : 0 < generationPrefactor γ
  one_generation : ∀ (N : ℕ) (hN : copyThreshold γ ≤ N) (n : BirthCount C N),
    (certifiedGeneration C hγ hmax N (copyThreshold_positive γ N hN) n).mass none ≤
      generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent)
  nonvacuous : ∀ (N : ℕ), copyThreshold γ ≤ N →
    generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent) ≤ 1/2
  lineage : ∀ (N : ℕ) (hN : copyThreshold γ ≤ N) (G : ℕ) (n : BirthCount C N),
    1-(G : ℝ)*(generationPrefactor γ*Real.exp (-(N : ℝ)*heredityExponent)) ≤
      lineageSuccess C hγ hmax N (copyThreshold_positive γ N hN) G n
  copy_tradeoff : ∀ (N G : ℕ) (hN : copyThreshold γ ≤ N), 1 ≤ G →
    ∀ (η : ℝ), 0 < η → Real.log (generationPrefactor γ*(G : ℝ)/η)/heredityExponent ≤ N →
    ∀ (n : BirthCount C N), 1-η ≤ lineageSuccess C hγ hmax N (copyThreshold_positive γ N hN) G n

theorem structural_transfer {γ : ℝ} (C : GrowthCertificate γ)
    (hγ : 0 < γ) (hmax : γ ≤ 1/100000000000) : HeredityConclusion C hγ hmax := {
  exponent_positive := heredityExponent_pos
  prefactor_positive := generationPrefactor_pos γ hγ
  one_generation := fun N hN n => certified_generation_failure C hγ hmax N
    (copyThreshold_positive γ N hN) (copyThreshold_large γ N hN) n
  nonvacuous := copyThreshold_nonvacuous γ hγ
  lineage := fun N hN G n => lineage_heredity_bound C hγ hmax N
    (copyThreshold_positive γ N hN) (copyThreshold_large γ N hN) G n
  copy_tradeoff := lineage_copy_tradeoff C hγ hmax }

end HeritableCompositions

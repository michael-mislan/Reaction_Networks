import proofs.CompositionalMemory.SourceTransmission
import proofs.HeritableCompositions.SourceBirthGeometry

namespace CompositionalMemory
open FiniteCopy CoreCouplingCAC HeritableCompositions

theorem source_word_birth_nonempty {k : ℕ} (N : ℕ)
    (hlarge : scalingCopyFloor ≤ N) (σ : Fin k → Bool) :
    Nonempty (WordBirthCount N (sourceWordCenter σ) σ) := by
  classical
  have hN : 1000000000000 ≤ N := by unfold scalingCopyFloor at hlarge; omega
  obtain ⟨n₀,_,h₀⟩ := low_initial_lattice_nonempty sourceWordLow sourceWordLow_spec.1 N hN
  obtain ⟨n₁,_,h₁⟩ := high_initial_lattice_nonempty sourceWordHigh sourceWordHigh_spec.1 N hN
  let n : Fin k → Counts := fun i => if σ i then n₁ else n₀
  refine ⟨⟨n,(mem_wordBirthCounts N (by omega) _ (sourceWordCenter_upper σ) σ n).mpr ?_⟩⟩
  intro i
  cases hσ : σ i <;>
    simp only [n,wordEnergy,sourceWordCenter,wordCenter,hσ,Bool.false_eq_true,
      if_false,if_true]
  · norm_num [innerEnergy,outerEnergy] at ⊢
    linarith only [h₀]
  · norm_num [innerEnergy,outerEnergy] at ⊢
    linarith only [h₁]

theorem source_word_readout {k : ℕ} (N : ℕ) (hN : 1 ≤ N) (σ : Fin k → Bool)
    (n : WordBirthCount N (sourceWordCenter σ) σ) (i : Fin k) :
    if σ i then 0 < compositionalReadout (n.val i)
    else compositionalReadout (n.val i) < 0 := by
  have he := (mem_wordBirthCounts N hN _ (sourceWordCenter_upper σ) σ n.val).mp n.property i
  cases hσ : σ i
  · simp only [Bool.false_eq_true,if_false]
    apply low_birth_readout sourceWordLow 0 sourceWordLow_spec.1 sourceWordLow_spec.2
      (by norm_num) (by norm_num) N hN
      ⟨n.val i,(mem_birthDomain _ N hN _).mpr ?_⟩
    simpa only [wordEnergy,sourceWordCenter,wordCenter,hσ,Bool.false_eq_true,if_false] using he
  · simp only [if_true]
    apply high_birth_readout sourceWordHigh 0 sourceWordHigh_spec.1 sourceWordHigh_spec.2
      (by norm_num) (by norm_num) N hN
      ⟨n.val i,(mem_birthDomain _ N hN _).mpr ?_⟩
    simpa only [wordEnergy,sourceWordCenter,wordCenter,hσ,if_true] using he

end CompositionalMemory

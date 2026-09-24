import proofs.CoreCouplingCAC.SourceAdapter
import proofs.CoreCouplingCAC.Preservation
import proofs.CoreCouplingCAC.Creation

namespace CoreCouplingCAC

/-- The current stationary result, with its actual source and quantifiers exposed.
Local trajectory selection is deliberately a separate pending theorem. -/
theorem stationary_core_assembly :
    (∀ p x, sourceDerivative p x =
      ![fA p x.A x.B x.z,fB p x.A x.B x.z,
        fZ p x.A x.B x.z x.H,fH p x.z x.H]) ∧
    (∀ i r, inputComplex (abSpecies i) (abReactions r) = coreInput i r ∧
      outputComplex (abSpecies i) (abReactions r) = coreOutput i r) ∧
    (∀ i r, inputComplex (zhSpecies i) (zhReactions r) = coreInput i r ∧
      outputComplex (zhSpecies i) (zhReactions r) = coreOutput i r) ∧
    CoreProductive 3 2 ∧
    (∀ j k, j = 0 ∨ k = 0 → ¬ CoreProductive j k) ∧
    (∀ S R, R.Nonempty → AutonomousRestriction S R → S = Finset.univ) ∧
    (∀ p, p.Positive → ∀ z A B C D, 0 < z → 0 < A → 0 < C →
      fA p A B z = 0 → fB p A B z = 0 →
      fA p C D z = 0 → fB p C D z = 0 → A = C ∧ B = D) ∧
    (∀ p, p.Positive → ∀ A B z H w K, 0 < A → 0 < z → 0 < w →
      fZ p A B z H = 0 → fH p z H = 0 →
      fZ p A B w K = 0 → fH p w K = 0 → z = w ∧ H = K) ∧
    (∀ p, p.Positive → 1 ≤ p.d → ∀ x y, x.Positive → y.Positive →
      Stationary p x → Stationary p y → x = y) ∧
    witnessRates.Positive ∧
    (∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      Stationary witnessRates x ∧ Stationary witnessRates y ∧ Stationary witnessRates w ∧
      x.z < y.z ∧ y.z < w.z) := by
  refine ⟨literal_source_adapter,AB_literal_core,ZH_literal_core,
    gain_two_core_productive,gain_two_core_reaction_minimal,core_species_minimal,?_,?_,
    loss_regime_unistationary,witnessRates_positive,repaired_source_multistationary⟩
  · intro p hp
    exact isolated_AB_unistationary p hp.2.2.2.2.1.le
  · intro p hp
    exact isolated_ZH_unistationary p hp.2.2.2.1 hp.2.2.2.2.2.le

end CoreCouplingCAC

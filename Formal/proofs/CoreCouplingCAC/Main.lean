import proofs.CoreCouplingCAC.StationaryAssembly
import proofs.CoreCouplingCAC.CreationRegime
import proofs.CoreCouplingCAC.Convergence
import proofs.CoreCouplingCAC.Boundary

open Filter Topology

namespace CoreCouplingCAC

/-- Forward trajectories of the literal mass-action source, with a true
coordinate limit and quantitative CAC production for all forward times. -/
def SourceSelected (L R : Fin 4 → ℝ) (c : State) : Prop :=
  ∀ x₀, Near c x₀ → ∃ X : ℝ → State, X 0 = x₀ ∧
    Tendsto (fun t => coordinates (X t)) atTop (𝓝 (coordinates c)) ∧
    ∀ t, 0 ≤ t →
      HasDerivAt (fun s => coordinates (X s)) (sourceDerivative witnessRates (X t)) t ∧
      (X t).Positive ∧
      energy L R (transform c) (transform (X t)) ≤
        energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t) ∧
      (1/10000:ℝ) ≤ (coreZH witnessRates (X t)).1 ∧
      (1/10000:ℝ) ≤ (coreZH witnessRates (X t)).2

theorem selected_source (L R : Fin 4 → ℝ) (c : State)
    (hw : ∀ i, (1/4:ℝ) ≤ L i/R i) (hs : Selected L R c) : SourceSelected L R c := by
  intro x₀ hx₀
  obtain ⟨X,hX₀,hX⟩ := hs x₀ hx₀
  refine ⟨X,hX₀,?_,?_⟩
  · apply transformed_convergence_source
    exact energy_decay_converges L R (transform c) (fun t => transform (X t))
      (energy L R (transform c) (transform x₀)) hw (fun t ht => (hX t ht).2.2.1)
  · intro t ht
    obtain ⟨hd,hp,he,ha,hb⟩ := hX t ht
    exact ⟨transformed_derivative_source witnessRates X t hd,hp,he,ha,hb⟩

/-- Scoped resolution of the guide's preservation/creation/selection target:
literal minimal cores, uniform clamped-module uniqueness, a noncreation
regime including its boundary, an interval of creation rates, and two
actually attracting CAC-active equilibria at one common parameter vector.
The last clauses expose the driven mass-balanced reservoir realization and
the ideal irreversible sink convention. No global-basin claim is made. -/
theorem coreCouplingCACResolution :
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
    (∀ e, (1/200000:ℝ) ≤ e → e ≤ (1/50000:ℝ) →
      (varyRates e).Positive ∧ ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
        Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
        x.z < y.z ∧ y.z < w.z) ∧
    witnessRates.Positive ∧
    (∃ c₁ c₂ : State, c₁.Positive ∧ c₂.Positive ∧
      Stationary witnessRates c₁ ∧ Stationary witnessRates c₂ ∧ c₁.z < c₂.z ∧
      SourceSelected lowLeft lowRight c₁ ∧ SourceSelected highLeft highRight c₂) ∧
    (∀ r : Fin 7,
      (∑ i : Fin 4, dynamicMass i*inputComplex i r) +
        (∑ i : Fin 5, externalMass i*externalInput i r) =
      (∑ i : Fin 4, dynamicMass i*outputComplex i r) +
        (∑ i : Fin 5, externalMass i*externalOutput i r)) ∧
    (∀ p x r, completedCurrent p x r = sourceCurrent p x r) ∧
    (∀ p, p.Positive → ∀ r : Fin 7, r ≠ 6 →
      forwardRate p r / reverseRate p r = Real.exp (chemicalAffinity p r)) ∧
    (∀ p, reverseRate p 6 = 0) := by
  refine ⟨literal_source_adapter,AB_literal_core,ZH_literal_core,
    gain_two_core_productive,gain_two_core_reaction_minimal,core_species_minimal,?_,?_,
    loss_regime_unistationary,?_,witnessRates_positive,?_,completed_mass_balance,
    buffered_current_agrees,reversible_rate_ratios,ideal_sink_declared⟩
  · intro p hp
    exact isolated_AB_unistationary p hp.2.2.2.2.1.le
  · intro p hp
    exact isolated_ZH_unistationary p hp.2.2.2.1 hp.2.2.2.2.2.le
  · intro e hl hr
    exact ⟨varyRates_positive e (by linarith),creation_interval e hl hr⟩
  · obtain ⟨c₁,c₂,hp₁,hp₂,hs₁,hs₂,hlt,hsel₁,hsel₂⟩ := two_selected_active_equilibria
    exact ⟨c₁,c₂,hp₁,hp₂,hs₁,hs₂,hlt,
      selected_source lowLeft lowRight c₁ low_weight_lower hsel₁,
      selected_source highLeft highRight c₂ high_weight_lower hsel₂⟩

end CoreCouplingCAC

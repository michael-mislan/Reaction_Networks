import proofs.OptimalAffinityRealizability.ResponseJet
import proofs.OptimalAffinityCorrected.FirstOrderRealizability

namespace OptimalAffinityRealizability

noncomputable section

def reconstructedReverseFlow {n : ℕ} (J : ℝ) (g q : Fin n → ℝ) : Fin n → ℝ :=
  fun i => OptimalAffinityCorrected.reconstructedReverseFlux J (g i) (q i)

def reconstructedForwardFlow {n : ℕ} (J : ℝ) (g q : Fin n → ℝ) : Fin n → ℝ :=
  fun i => OptimalAffinityCorrected.reconstructedForwardFlux J (g i) (q i)

theorem reconstructedFlows_positive {n : ℕ} (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i) :
    (∀ i, 0 < reconstructedReverseFlow J g q i) ∧
    (∀ i, 0 < reconstructedForwardFlow J g q i) := by
  constructor <;> intro i
  · exact (OptimalAffinityCorrected.reconstructedFluxes_firstOrder
      J (g i) (q i) hJ (hg i) (hq i)).1
  · exact (OptimalAffinityCorrected.reconstructedFluxes_firstOrder
      J (g i) (q i) hJ (hg i) (hq i)).2.1

theorem reconstructedFlows_tightCoupling {n : ℕ} (J : ℝ)
    (g q : Fin n → ℝ) (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) :
    ∀ i, reconstructedForwardFlow J g q i -
      reconstructedReverseFlow J g q i = J * g i := by
  intro i
  exact (OptimalAffinityCorrected.reconstructedFluxes_firstOrder
    J (g i) (q i) hJ (hg i) (hq i)).2.2.1

theorem reconstructedFlows_derivativeBalance {n : ℕ} (J : ℝ)
    (g q f h : Fin n → ℝ) (hq : ∀ i, 1 < q i)
    (hh : ∀ i, h i = q i * f i) :
    ∀ i, reconstructedForwardFlow J g q i * f i =
      reconstructedReverseFlow J g q i * h i := by
  intro i
  rw [hh i]
  unfold reconstructedForwardFlow reconstructedReverseFlow
  unfold OptimalAffinityCorrected.reconstructedForwardFlux
    OptimalAffinityCorrected.reconstructedReverseFlux
  field_simp [ne_of_gt (sub_pos.mpr (hq i))]

def sourceWithReconstructedRates {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q : Fin n → ℝ) (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) : SquareSource n where
  reactant := source.reactant
  product := source.product
  forwardRate := reconstructedForwardFlow J g q
  reverseRate := reconstructedReverseFlow J g q
  controlled := source.controlled
  reactant_nonnegative := source.reactant_nonnegative
  product_nonnegative := source.product_nonnegative
  forwardRate_positive := (reconstructedFlows_positive J g q hJ hg hq).2
  reverseRate_positive := (reconstructedFlows_positive J g q hJ hg hq).1
  reactant_det_isUnit := source.reactant_det_isUnit
  netStoich_det_isUnit := source.netStoich_det_isUnit

/-- The source constructor is used only with the positive interior hypotheses;
this theorem exposes its actual rate positivity rather than hiding it in a
realizability predicate. -/
theorem sourceWithReconstructedRates_positive {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q : Fin n → ℝ) (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) :
    (∀ i, 0 < (sourceWithReconstructedRates source J g q hJ hg hq).forwardRate i) ∧
    (∀ i, 0 < (sourceWithReconstructedRates source J g q hJ hg hq).reverseRate i) := by
  exact ⟨(reconstructedFlows_positive J g q hJ hg hq).2,
    (reconstructedFlows_positive J g q hJ hg hq).1⟩

def netUnitStateDrift {n : ℕ} (source : SquareSource n) (J : ℝ)
    (g q : Fin n → ℝ) : Fin n → ℝ :=
  source.netStoich.mulVec (fun i =>
    reconstructedForwardFlow J g q i - reconstructedReverseFlow J g q i)

/-- Tight coupling transports the reconstructed reaction current through the
literal stoichiometric matrix. -/
theorem netUnitStateDrift_eq_scale_productionMode {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i) :
    netUnitStateDrift source J g q = J • source.netStoich.mulVec g := by
  unfold netUnitStateDrift
  have hcurr : (fun i => reconstructedForwardFlow J g q i -
      reconstructedReverseFlow J g q i) = J • g := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact reconstructedFlows_tightCoupling J g q hJ hg hq i
  rw [hcurr, Matrix.mulVec_smul]

/-- Every noncontrolled species is stationary at the all-one state. -/
theorem reconstructedSource_noncontrolled_stationary {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g) :
    ∀ i, i ≠ source.controlled → netUnitStateDrift source J g q i = 0 := by
  intro i hi
  rw [netUnitStateDrift_eq_scale_productionMode source J g q hJ hg hq]
  simp [Pi.smul_apply, hmode i, hi]

/-- The controlled species carries exactly the chosen positive production
current at the all-one state. -/
theorem reconstructedSource_controlled_current {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i) (hq : ∀ i, 1 < q i)
    (hmode : ControlledProductionMode source g) :
    netUnitStateDrift source J g q source.controlled = J := by
  rw [netUnitStateDrift_eq_scale_productionMode source J g q hJ hg hq]
  simp [Pi.smul_apply, hmode source.controlled]

structure FirstOrderSourceRealization {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q f h : Fin n → ℝ) : Prop where
  positiveRates :
    (∀ i, 0 < reconstructedForwardFlow J g q i) ∧
    (∀ i, 0 < reconstructedReverseFlow J g q i)
  tightCoupling : ∀ i, reconstructedForwardFlow J g q i -
    reconstructedReverseFlow J g q i = J * g i
  derivativeBalance : ∀ i, reconstructedForwardFlow J g q i * f i =
    reconstructedReverseFlow J g q i * h i
  noncontrolledStationary : ∀ i, i ≠ source.controlled →
    netUnitStateDrift source J g q i = 0
  controlledCurrent : netUnitStateDrift source J g q source.controlled = J

theorem exists_firstOrderSourceRealization {n : ℕ} (source : SquareSource n)
    (J : ℝ) (g q f h : Fin n → ℝ) (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hq : ∀ i, 1 < q i) (hh : ∀ i, h i = q i * f i)
    (hmode : ControlledProductionMode source g) :
    FirstOrderSourceRealization source J g q f h := by
  exact {
    positiveRates := ⟨(reconstructedFlows_positive J g q hJ hg hq).2,
      (reconstructedFlows_positive J g q hJ hg hq).1⟩
    tightCoupling := reconstructedFlows_tightCoupling J g q hJ hg hq
    derivativeBalance := reconstructedFlows_derivativeBalance J g q f h hq hh
    noncontrolledStationary := reconstructedSource_noncontrolled_stationary
      source J g q hJ hg hq hmode
    controlledCurrent := reconstructedSource_controlled_current
      source J g q hJ hg hq hmode
  }

end
end OptimalAffinityRealizability

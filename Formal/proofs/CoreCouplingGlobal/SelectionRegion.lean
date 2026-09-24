import proofs.CoreCouplingGlobal.SublevelLimit
import proofs.CoreCouplingGlobal.ScalarBarrier

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

def InSelectionRegion (s : State) : Prop :=
  s.A+s.B ≤ 34 ∧ s.z+(7/4:ℝ)*s.H ≤ 384 ∧ s.z ≤ 12 ∧ 2 ≤ s.B

theorem selection_region_forward (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (h0 : InSelectionRegion (X 0)) :
    ∀ t, 0 ≤ t → InSelectionRegion (X t) ∧ InResponseBox (X t) := by
  obtain ⟨hS0,hW0,hz0,hB0⟩ := h0
  have hS : ∀ t, 0 ≤ t → (X t).A+(X t).B ≤ 34 := by
    apply scalar_upper_barrier _ _ 34 (fun t ht => (hX.dA t ht).add (hX.dB t ht)) hS0
    intro t ht hlarge
    change 34 ≤ (X t).A+(X t).B at hlarge
    have hc := total_upper_comparison (X t).A (X t).B (X t).z e (hX.positive t ht).1.le he
    have hm := mul_nonneg (show 0 ≤ 1-e by linarith) (show 0 ≤ (X t).A+(X t).B-34 by linarith)
    nlinarith
  have hW : ∀ t, 0 ≤ t → (X t).z+(7/4:ℝ)*(X t).H ≤ 384 := by
    apply scalar_upper_barrier _ _ 384
      (fun t ht => (hX.dz t ht).add ((hX.dH t ht).const_mul (7/4))) hW0
    intro t ht hlarge
    change 384 ≤ (X t).z+(7/4:ℝ)*(X t).H at hlarge
    have hp := hX.positive t ht
    have hst := hS t ht
    have hc := weighted_upper_comparison (X t).A (X t).B (X t).z (X t).H e
      (by linarith [hp.2.1]) hp.2.1.le hp.2.2.1.le hp.2.2.2.le
    linarith
  have hz : ∀ t, 0 ≤ t → (X t).z ≤ 12 := by
    apply scalar_upper_barrier _ _ 12 hX.dz hz0
    intro t ht hlarge
    have hp := hX.positive t ht
    have hst := hS t ht
    have hc := z_entry_drift (X t).A (X t).B (X t).z (X t).H e
      (by linarith [hp.2.1]) hp.2.1.le hlarge (hW t ht)
    linarith
  have hB : ∀ t, 0 ≤ t → 2 ≤ (X t).B := by
    apply scalar_lower_barrier _ _ 2 hX.dB hB0
    intro t ht hsmall
    have hp := hX.positive t ht
    have hc := B_entry_drift (X t).A (X t).B (X t).z e hp.1.le hp.2.1.le hsmall (hz t ht) he hu
    linarith
  intro t ht
  have hp := hX.positive t ht
  have hst := hS t ht
  have hwt := hW t ht
  refine ⟨⟨hst,hwt,hz t ht,hB t ht⟩,?_⟩
  exact ⟨hp.1.le,by linarith [hp.2.1],hB t ht,by linarith [hp.1],
    hp.2.2.1.le,hz t ht,hp.2.2.2.le,by linarith [hp.2.2.1]⟩

/-- The certified rule depends only on the initial concentrations and their energy. -/
theorem initial_state_sublevel_selector (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ p : PotentialPrimitives e, ∃ low mid high : State,
      low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∀ X : ℝ → State, IsPositiveTrajectory e X → InSelectionRegion (X 0) →
        statePotential e p (X 0) < statePotential e p mid →
        ((X 0).B < mid.B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high))) ∧
        (mid.B < (X 0).B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) := by
  obtain ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hsel⟩ := classified_sublevel_selector e hl hu
  refine ⟨p,low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,?_⟩
  intro X hX h0 henergy
  apply hsel X hX 0 (by norm_num) _ henergy
  intro t ht
  exact (selection_region_forward e (by linarith) hu X hX h0 t ht).2

end CoreCouplingGlobal

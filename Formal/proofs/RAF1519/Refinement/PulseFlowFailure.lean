import proofs.RAF1519.Refinement.PulseFlowLaw
import proofs.RAF1519.Refinement.KernelFailure

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal
set_option maxHeartbeats 40000

theorem pulseFlow_operating_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    pulseFlowLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {z | ¬operatingSuccess V z} ≤
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) := by
  have hV0 : (0:ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  have hb := kernel_failure_bound (graphPulsePMF N p).toMeasure
    (pulseFlowKernel hn r d k V hr0 hd0 hk hV0 N p)
    {o | ¬CountPrepared V (postPulseState N V p o)} (Set.to_countable _).measurableSet
    {z | ¬operatingSuccess V z} (operatingSuccess_measurable V).compl
    (24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3)))) ?_
  · calc
      _ ≤ (graphPulsePMF N p).toMeasure {o | ¬CountPrepared V (postPulseState N V p o)}+
          24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) := hb
      _ ≤ 5*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3)))+
          24*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) :=
        add_le_add (graphPulse_preparation_root_failure N V hV Δ hΔ p hready) le_rfl
      _ = _ := by ring
  · intro o ho
    have hp : CountPrepared V (postPulseState N V p o) := not_not.mp ho
    exact molecular_operating_failure hn r d k V Δ hV0 hΔ hr hd hk hsym hdegree
      (postPulseState N V p o) hp.1 hp.2.1 hp.2.2

#print axioms pulseFlow_operating_failure

end
end RAF1519.Refinement

import proofs.RAF1519.Refinement.IntegerCycleMeasurable
import proofs.RAF1519.Refinement.PulseFlowFailure

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped BigOperators ENNReal
set_option maxHeartbeats 40000

theorem molecular_integer_transfer {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < (V:ℝ)) (N : MolecularState n) (p : Fin n → Intervention) :
    ∀ᵐ z ∂molecularLaw hn r d k V hr hd hk hV N,
      operatingSuccess V z → integerCycleSuccess V p z := by
  filter_upwards [molecular_wait_positive hn r d k V hr hd hk hV N,
    molecular_nonexplosive hn r d k V hr hd hk hV N] with z hwait hdiv
  intro hs
  have hevent : ∀ᶠ K in atTop, 4 < waitingSum (fun i => (z (i+1)).2.2) K :=
    hdiv.eventually (eventually_gt_atTop 4)
  obtain ⟨K,hK⟩ := hevent.exists
  have hclock : 4 < prefixElapsed K (Preorder.frestrictLe K z) := by
    rw [prefix_elapsed_holdingClock]
    unfold holdingClock
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (z (i+1)).2.2) K]
    exact hK
  exact integerCycleSuccess_of_operating V hV p z (fun j => (hwait j).le) K hclock hs

theorem pulseFlow_integer_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℕ) (hV : 10000 ≤ V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n) (p : Fin n → Intervention)
    (hready : ∀ i, Ready (1/100) (concentration V (fun s => N (i,s)))) :
    pulseFlowLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk (by exact_mod_cast (show 0 < V by omega)) N p
      {z | ¬integerCycleSuccess V p z} ≤
      29*n*ENNReal.ofReal (Real.exp (-(V:ℝ)/(200000000000000*(1+Δ)^3))) := by
  have hV0 : (0:ℝ) < V := by exact_mod_cast (show 0 < V by omega)
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  have hmeas : MeasurableSet {z : MolecularPath n | operatingSuccess V z → integerCycleSuccess V p z} := by
    simpa only [imp_iff_not_or,Set.setOf_or] using
      (operatingSuccess_measurable (n := n) V).compl.union (integerCycleSuccess_measurable V p)
  have htransfer : ∀ᵐ z ∂pulseFlowLaw hn r d k V hr0 hd0 hk hV0 N p,
      operatingSuccess V z → integerCycleSuccess V p z := by
    apply Measure.ae_comp_of_ae_ae hmeas
    exact Filter.Eventually.of_forall (fun o =>
      molecular_integer_transfer hn r d k V hr0 hd0 hk hV0 (postPulseState N V p o) p)
  apply le_trans (measure_mono_ae ?_) (pulseFlow_operating_failure hn r d k V hV Δ hΔ hr hd hk hsym hdegree N p hready)
  filter_upwards [htransfer] with z hz
  exact fun hf hs => hf (hz hs)

#print axioms pulseFlow_integer_failure

end
end RAF1519.Refinement


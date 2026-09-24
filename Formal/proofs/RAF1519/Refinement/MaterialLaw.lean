import proofs.RAF1519.Refinement.MaterialTime
import proofs.RAF1519.Refinement.CountNonexplosion
import proofs.RandomViability.JumpInitial

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped BigOperators
set_option maxHeartbeats 30000

/-- The hypotheses needed by the path comparison hold under the unrestricted
    molecular law; only the already-estimated noise event remains conditional. -/
theorem molecular_material_return {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n)
    (h0 : ∀ b i, |materialNode b V N i-1| ≤ 1/25) :
    ∀ᵐ z ∂molecularLaw hn r d k V hr hd hk hV N,
      (∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V)) →
      (∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1) ∧
      (∀ b i, |countMaterial b V z 4 i-1| < 1/1000) := by
  have hi := jumpTrajectory_initial_population N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr hd hk hV.le)
    (molecular_total_positive hn r d k V hr hd hk hV)
  have hc := jumpTrajectory_consistent N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr hd hk hV.le)
    (molecular_total_positive hn r d k V hr hd hk hV)
  filter_upwards [hi,hc,molecular_wait_positive hn r d k V hr hd hk hV N,
    molecular_nonexplosive hn r d k V hr hd hk hV N] with z hinit hcons hwait hdiv
  intro hnoise
  have hz0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25 := by
    rw [hinit]
    exact h0
  have hevent : ∀ᶠ K in atTop, 4 < waitingSum (fun i => (z (i+1)).2.2) K :=
    hdiv.eventually (eventually_gt_atTop 4)
  obtain ⟨K,hK⟩ := hevent.exists
  have hclock : 4 < prefixElapsed K (Preorder.frestrictLe K z) := by
    rw [prefix_elapsed_holdingClock]
    unfold holdingClock
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (z (i+1)).2.2) K]
    exact hK
  exact ⟨material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hwait hcons hnoise hz0,
    fun b i => material_return_four r d k V Δ hV hΔ hk hsym hdegree z hwait hcons hnoise hz0 K hclock b i⟩

#print axioms molecular_material_return

end
end RAF1519.Refinement

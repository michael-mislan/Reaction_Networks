import proofs.RAF1519.Refinement.OperatingEvent
import proofs.RAF1519.Refinement.MarkFailureBudget
import proofs.RAF1519.Refinement.MaterialLaw

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped BigOperators ENNReal
set_option maxHeartbeats 50000

/-- Unconditional operating-period failure under the unrestricted physical law.
    The input is the actual post-pulse state; pulse failures are paid separately. -/
theorem molecular_operating_failure {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ) (N : MolecularState n)
    (h0 : ∀ b i, |materialNode b V N i-1| ≤ 1/25)
    (hD : ∀ i, (N (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => N (i,s)))) :
    molecularLaw hn r d k V (fun i => le_trans (by norm_num) (hr i).1)
      (fun i => le_trans (by norm_num) (hd i).1) hk hV N {z | ¬operatingSuccess V z} ≤
      24*n*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  let hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (by norm_num) (hr i).1
  let hd0 : ∀ i, 0 ≤ d i := fun i => le_trans (by norm_num) (hd i).1
  let Bad := (⋃ p, countIntervalFailure r d k V Δ p (materialExit V)) ∪
    (⋃ p : Fin n × PhysicalMark, markIntervalFailure r d k V p.1 p.2 (materialExit V))
  have hi := jumpTrajectory_initial_population N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr0 hd0 hk hV.le)
    (molecular_total_positive hn r d k V hr0 hd0 hk hV)
  have hc := jumpTrajectory_consistent N (molecularNext r d k) (molecularRate r d k V)
    (molecular_rate_nonnegative r d k V hr0 hd0 hk hV.le)
    (molecular_total_positive hn r d k V hr0 hd0 hk hV)
  have hs : ∀ᵐ z ∂molecularLaw hn r d k V hr0 hd0 hk hV N,
      z ∉ Bad → operatingSuccess V z := by
    filter_upwards [hi,hc,molecular_wait_positive hn r d k V hr0 hd0 hk hV N,
      molecular_nonexplosive hn r d k V hr0 hd0 hk hV N] with z hinit hcons hwait hdiv
    intro hz
    have hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V) := by
      intro p hp
      exact hz (Or.inl (Set.mem_iUnion.mpr ⟨p,hp⟩))
    have hmarks : ∀ i m, z ∉ markIntervalFailure r d k V i m (materialExit V) := by
      intro i m hp
      exact hz (Or.inr (Set.mem_iUnion.mpr ⟨(i,m),hp⟩))
    have hevent : ∀ᶠ K in atTop, 4 < waitingSum (fun i => (z (i+1)).2.2) K :=
      hdiv.eventually (eventually_gt_atTop 4)
    obtain ⟨K,hK⟩ := hevent.exists
    have hclock : 4 < prefixElapsed K (Preorder.frestrictLe K z) := by
      rw [prefix_elapsed_holdingClock]
      unfold holdingClock
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (z (i+1)).2.2) K]
      exact hK
    apply operatingSuccess_of_noise r d k V Δ hV hΔ hr hd hk hsym hdegree z hwait hcons hnoise hmarks
      _ _ _ K hclock
    · rw [hinit]; exact h0
    · rw [hinit]; exact hD
    · rw [hinit]; exact hY
  have hb := molecular_operating_noise_tail hn r d k V Δ
    (fun i => ⟨hr0 i,(hr i).2⟩) (fun i => ⟨hd0 i,(hd i).2⟩)
    hk hV hΔ hsym hdegree N (materialExit V) (materialExit_measurable V)
  apply le_trans (measure_mono_ae ?_) hb
  filter_upwards [hs] with z hz
  intro hfail
  by_contra hnb
  exact hfail (hz hnb)

#print axioms molecular_operating_failure

end
end RAF1519.Refinement

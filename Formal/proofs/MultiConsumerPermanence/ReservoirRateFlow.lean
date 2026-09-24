import proofs.MultiConsumerPermanence.ReservoirRateSource
import proofs.MultiConsumerPermanence.ReservoirFlow
import proofs.MultiConsumerPermanence.RateFlow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

noncomputable def reservoirRateDonorVector {n : ℕ} (r : ReservoirRates n)
    (y : ReservoirVector n) : ConsumerVector :=
  ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3),
    y (.inl 4)*copyingLoad r.reactions (fun i => y (.inr i))]

noncomputable def reservoirPerturbedField {n : ℕ} (r : ReservoirRates n)
    (y : ReservoirVector n) : ReservoirVector n :=
  Sum.elim (fun i => if i = 4 then r.feed-r.wash*y (.inl 4)-
      y (.inl 4)*y (.inl 2)*copyingLoad r.reactions (fun j => y (.inr j))
    else rateField (baseRates r.reactions) (reservoirRateDonorVector r y) i)
    (fun i => y (.inr i)*(r.reactions.k i*(y (.inl 4)*y (.inl 2))-
      r.reactions.mu i-r.reactions.rho i*y (.inr i)))

theorem reservoirPerturbedField_contDiff {n : ℕ} (r : ReservoirRates n) :
    ContDiff ℝ 1 (reservoirPerturbedField r) := by
  apply contDiff_pi.2
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [reservoirPerturbedField,rateField,reservoirRateDonorVector,
      copyingLoad,rateA,rateB,rateZ,rateH,baseRates] <;> fun_prop
  | inr i =>
    simp only [reservoirPerturbedField,Sum.elim_inr]
    fun_prop

theorem reservoir_rate_extension_solution {n : ℕ} (r : ReservoirRates n) (R : ℝ)
    (hR : 0 < R) (x₀ : ReservoirVector n) :
    ∃ b : ReservoirVector n → ℝ, ∃ X : ℝ → ReservoirVector n,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (reservoirPart (X t)) • reservoirPerturbedField r (reservoirPart (X t))) t := by
  let b : ContDiffBump (0 : ReservoirVector n) := ⟨R,2*R,hR,by linarith⟩
  let f : ReservoirVector n → ReservoirVector n := fun x => b x • reservoirPerturbedField r x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (reservoirPerturbedField_contDiff r)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (reservoirPart x)) := by
    simpa only [mul_one] using hK.comp (reservoirPart_lipschitz n)
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (reservoirPart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem reservoirRateDonorVector_nonneg {n : ℕ} (r : ReservoirRates n)
    (hk : ∀ i, 0 ≤ r.reactions.k i) (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ reservoirRateDonorVector r y i := by
  intro i
  fin_cases i
  · exact hy (.inl 0)
  · exact hy (.inl 1)
  · exact hy (.inl 2)
  · exact hy (.inl 3)
  · exact mul_nonneg (hy (.inl 4)) (copying_load_nonneg _ _ hk (fun i => hy (.inr i)))

theorem reservoir_rate_boundary_nonneg {n : ℕ} (r : ReservoirRates n)
    (hr : RateBox (baseRates r.reactions)) (hk : ∀ i, 0 ≤ r.reactions.k i) (hf : 0 ≤ r.feed)
    (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) (i : Fin 5 ⊕ Fin n)
    (hi : y i = 0) : 0 ≤ reservoirPerturbedField r y i := by
  cases i with
  | inl i =>
    fin_cases i
    · exact rate_boundary_nonneg _ hr _ (reservoirRateDonorVector_nonneg r hk y hy) 0 hi
    · exact rate_boundary_nonneg _ hr _ (reservoirRateDonorVector_nonneg r hk y hy) 1 hi
    · exact rate_boundary_nonneg _ hr _ (reservoirRateDonorVector_nonneg r hk y hy) 2 hi
    · exact rate_boundary_nonneg _ hr _ (reservoirRateDonorVector_nonneg r hk y hy) 3 hi
    · change y (.inl 4) = 0 at hi
      simpa [reservoirPerturbedField,hi] using hf
  | inr i => simp [reservoirPerturbedField,hi]

theorem reservoir_rate_extension_nonnegative {n : ℕ} (r : ReservoirRates n)
    (hr : RateBox (baseRates r.reactions)) (hk : ∀ i, 0 ≤ r.reactions.k i) (hf : 0 ≤ r.feed)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x) (X : ℝ → ReservoirVector n)
    (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (reservoirPart (X t)) • reservoirPerturbedField r (reservoirPart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (reservoirPart (X t))*reservoirPerturbedField r (reservoirPart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply reservoir_rate_boundary_nonneg r hr hk hf _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

end MultiConsumerPermanence

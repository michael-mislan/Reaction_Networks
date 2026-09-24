import proofs.MultiConsumerPermanence.ReservoirSource
import proofs.MultiConsumerPermanence.Flow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

abbrev ReservoirVector (n : ℕ) := (Fin 5 ⊕ Fin n) → ℝ

noncomputable def reservoirDonorVector {n : ℕ} (y : ReservoirVector n) : ConsumerVector :=
  ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3),y (.inl 4)*total (fun i => y (.inr i))]

noncomputable def reservoirField {n : ℕ} (e feed wash : ℝ) (y : ReservoirVector n) : ReservoirVector n :=
  Sum.elim (fun i => if i = 4 then feed-wash*y (.inl 4)-y (.inl 4)*y (.inl 2)*total (fun j => y (.inr j))
    else consumerField e (reservoirDonorVector y) i)
    (fun i => y (.inr i)*(y (.inl 4)*y (.inl 2)-1/2-(n:ℝ)*y (.inr i)))

def reservoirPart {n : ℕ} (y : ReservoirVector n) : ReservoirVector n := fun i => max 0 (y i)

theorem reservoirPart_lipschitz (n : ℕ) : LipschitzWith 1 (@reservoirPart n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (reservoirPart x i) (reservoirPart y i) ≤ dist (x i) (y i) := by
      have hh := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
      simpa only [reservoirPart,id_eq,NNReal.coe_one,one_mul] using hh
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem reservoirField_contDiff (n : ℕ) (e feed wash : ℝ) :
    ContDiff ℝ 1 (@reservoirField n e feed wash) := by
  apply contDiff_pi.2
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [reservoirField,consumerField,reservoirDonorVector,total,
      fA,fB,fZ,fH,flagshipRates] <;> fun_prop
  | inr i =>
    simp only [reservoirField,Sum.elim_inr]
    fun_prop

theorem reservoir_extension_solution (n : ℕ) (e feed wash R : ℝ) (hR : 0 < R)
    (x₀ : ReservoirVector n) :
    ∃ b : ReservoirVector n → ℝ, ∃ X : ℝ → ReservoirVector n,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (reservoirPart (X t)) • reservoirField e feed wash (reservoirPart (X t))) t := by
  let b : ContDiffBump (0 : ReservoirVector n) := ⟨R,2*R,hR,by linarith⟩
  let f : ReservoirVector n → ReservoirVector n := fun x => b x • reservoirField e feed wash x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (reservoirField_contDiff n e feed wash)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (reservoirPart x)) := by
    simpa only [mul_one] using hK.comp (reservoirPart_lipschitz n)
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (reservoirPart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem reservoirDonorVector_nonneg {n : ℕ} (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) :
    ∀ i, 0 ≤ reservoirDonorVector y i := by
  intro i
  fin_cases i
  · exact hy (.inl 0)
  · exact hy (.inl 1)
  · exact hy (.inl 2)
  · exact hy (.inl 3)
  · exact mul_nonneg (hy (.inl 4)) (total_nonneg _ (fun i => hy (.inr i)))

theorem reservoir_boundary_nonneg {n : ℕ} (e feed wash : ℝ) (he : 0 ≤ e) (hf : 0 ≤ feed)
    (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) (i : Fin 5 ⊕ Fin n)
    (hi : y i = 0) : 0 ≤ reservoirField e feed wash y i := by
  cases i with
  | inl i =>
    fin_cases i
    · exact consumer_boundary_nonneg e he (reservoirDonorVector y) (reservoirDonorVector_nonneg y hy) 0 hi
    · exact consumer_boundary_nonneg e he (reservoirDonorVector y) (reservoirDonorVector_nonneg y hy) 1 hi
    · exact consumer_boundary_nonneg e he (reservoirDonorVector y) (reservoirDonorVector_nonneg y hy) 2 hi
    · exact consumer_boundary_nonneg e he (reservoirDonorVector y) (reservoirDonorVector_nonneg y hy) 3 hi
    · change y (.inl 4) = 0 at hi
      simpa [reservoirField,hi] using hf
  | inr i => simp [reservoirField,hi]

theorem reservoir_extension_nonnegative {n : ℕ} (e feed wash : ℝ) (he : 0 ≤ e) (hf : 0 ≤ feed)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x) (X : ℝ → ReservoirVector n)
    (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (reservoirPart (X t)) • reservoirField e feed wash (reservoirPart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (reservoirPart (X t))*reservoirField e feed wash (reservoirPart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply reservoir_boundary_nonneg e feed wash he hf _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

end MultiConsumerPermanence

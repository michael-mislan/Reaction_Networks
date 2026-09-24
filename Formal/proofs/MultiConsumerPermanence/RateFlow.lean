import proofs.MultiConsumerPermanence.RateBounds
import proofs.MultiConsumerPermanence.RateComposition
import proofs.RobustPermanence.RateFlowBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Set
open scoped BigOperators

theorem near_consumer_box {n : ℕ} (hn : 0 < n) (e delta : ℝ) (r : Rates n)
    (h : Near e delta r) (hd : delta ≤ rateRadius) (i : Fin n) :
    r.k i ∈ Icc (1/2:ℝ) 2 ∧ r.mu i ∈ Icc (0:ℝ) 1 ∧
      r.rho i ∈ Icc ((n:ℝ)/2) ((n:ℝ)+1) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hk := abs_le.mp (h.k i)
  have hm := abs_le.mp (h.mu i)
  have hr := abs_le.mp (h.rho i)
  dsimp [rateRadius] at hd
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

noncomputable def rateDonorVector {n : ℕ} (r : Rates n) (y : Vector n) : ConsumerVector :=
  ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3),copyingLoad r (fun i => y (.inr i))]

noncomputable def perturbedField {n : ℕ} (r : Rates n) (y : Vector n) : Vector n :=
  Sum.elim (fun i => rateField (baseRates r) (rateDonorVector r y) i.castSucc)
    (fun i => y (.inr i)*(r.k i*y (.inl 2)-r.mu i-r.rho i*y (.inr i)))

theorem perturbedField_contDiff {n : ℕ} (r : Rates n) : ContDiff ℝ 1 (perturbedField r) := by
  apply contDiff_pi.2
  intro i
  cases i with
  | inl i =>
    fin_cases i <;> simp [perturbedField,rateField,rateDonorVector,copyingLoad,rateA,rateB,rateZ,rateH] <;> fun_prop
  | inr i =>
    simp only [perturbedField,Sum.elim_inr]
    fun_prop

theorem perturbed_extension_solution {n : ℕ} (r : Rates n) (R : ℝ) (hR : 0 < R) (x₀ : Vector n) :
    ∃ b : Vector n → ℝ, ∃ X : ℝ → Vector n,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (positivePart (X t)) • perturbedField r (positivePart (X t))) t := by
  let b : ContDiffBump (0 : Vector n) := ⟨R,2*R,hR,by linarith⟩
  let f : Vector n → Vector n := fun x => b x • perturbedField r x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (perturbedField_contDiff r)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (positivePart x)) := by
    simpa only [mul_one] using hK.comp (positivePart_lipschitz n)
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (positivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem copying_load_nonneg {n : ℕ} (r : Rates n) (x : Fin n → ℝ)
    (hk : ∀ i, 0 ≤ r.k i) (hx : ∀ i, 0 ≤ x i) : 0 ≤ copyingLoad r x :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hk i) (hx i))

theorem copying_load_le_twice {n : ℕ} (r : Rates n) (x : Fin n → ℝ)
    (hk : ∀ i, r.k i ≤ 2) (hx : ∀ i, 0 ≤ x i) : copyingLoad r x ≤ 2*total x := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hk i) (hx i))
  simpa only [copyingLoad,total,Finset.mul_sum] using hh

theorem rateDonorVector_nonneg {n : ℕ} (r : Rates n) (y : Vector n)
    (hk : ∀ i, 0 ≤ r.k i) (hy : ∀ i, 0 ≤ y i) : ∀ i, 0 ≤ rateDonorVector r y i := by
  intro i
  fin_cases i
  · exact hy (.inl 0)
  · exact hy (.inl 1)
  · exact hy (.inl 2)
  · exact hy (.inl 3)
  · exact copying_load_nonneg r _ hk (fun i => hy (.inr i))

theorem perturbed_boundary_nonneg {n : ℕ} (r : Rates n) (hr : RateBox (baseRates r))
    (hk : ∀ i, 0 ≤ r.k i) (y : Vector n) (hy : ∀ i, 0 ≤ y i)
    (i : Fin 4 ⊕ Fin n) (hi : y i = 0) : 0 ≤ perturbedField r y i := by
  cases i with
  | inl i =>
    apply rate_boundary_nonneg (baseRates r) hr _ (rateDonorVector_nonneg r y hk hy) i.castSucc
    fin_cases i <;> exact hi
  | inr i => simp [perturbedField,hi]

theorem perturbed_extension_nonnegative {n : ℕ} (r : Rates n) (hr : RateBox (baseRates r))
    (hk : ∀ i, 0 ≤ r.k i) (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (positivePart (X t)) • perturbedField r (positivePart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (positivePart (X t))*perturbedField r (positivePart (X t)) i) 0
    (fun t _ => hasDerivAt_pi.1 (hd t) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply perturbed_boundary_nonneg r hr hk _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

end MultiConsumerPermanence

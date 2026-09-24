import proofs.MultiConsumerPermanence.RateFlow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

theorem perturbed_extension_total_bound {n : ℕ} (r : Rates n) (hr : RateBox (baseRates r)) (S : ℝ)
    (hS : 34 ≤ S) (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 0)+X 0 (.inl 1) ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • perturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateA (baseRates r) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2))+rateB (baseRates r) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)))) S ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 0)).add ((hasDerivAt_pi.1 (hd t ht)) (.inl 1)) using 1
    dsimp [perturbedField,rateField,rateDonorVector]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_total_upper (baseRates r) hr (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (hX t ht (.inl 0)) (hX t ht (.inl 1))
    linarith only [hh,hs,hS]

theorem perturbed_extension_weighted_bound {n : ℕ} (r : Rates n) (hr : RateBox (baseRates r))
    (hk : ∀ i, 0 ≤ r.k i) (S W : ℝ)
    (hW : (7/2)*(2*S+200) ≤ W) (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S) (h0 : X 0 (.inl 2)+(7/4:ℝ)*X 0 (.inl 3) ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • perturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 2)+(7/4:ℝ)*X t (.inl 3) ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateZ (baseRates r) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) (copyingLoad r (fun i => X t (.inr i)))+(7/4:ℝ)*rateH (baseRates r) (X t (.inl 2)) (X t (.inl 3)))) W ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 2)).add (((hasDerivAt_pi.1 (hd t ht)) (.inl 3)).const_mul (7/4:ℝ)) using 1
    dsimp [perturbedField,rateField,rateDonorVector]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_weighted_general (baseRates r) hr (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) (copyingLoad r (fun i => X t (.inr i))) S
      (hX t ht (.inl 0)) (by have hh := hS t ht; have hn := hX t ht (.inl 1); linarith)
      (hX t ht (.inl 1)) (hX t ht (.inl 2)) (hX t ht (.inl 3)) (copying_load_nonneg r _ hk (fun i => hX t ht (.inr i)))
    linarith only [hh,hw,hW]


theorem perturbed_extension_aggregate_deriv {n : ℕ} (r : Rates n)
    (b : Vector n → ℝ) (X : ℝ → Vector n) (t : ℝ)
    (hd : HasDerivAt X (b (X t) • perturbedField r (X t)) t) :
    HasDerivAt (fun s => total (fun i => X s (.inr i)))
      (b (X t)*(growthTotal r (X t (.inl 2)) (fun i => X t (.inr i))-
        lossTotal r (fun i => X t (.inr i)))) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_pi.1 hd (.inr i))
  have hi : (∑ i, X t (.inr i)*(r.k i*X t (.inl 2)-r.mu i-r.rho i*X t (.inr i))) =
      growthTotal r (X t (.inl 2)) (fun i => X t (.inr i))-lossTotal r (fun i => X t (.inr i)) := by
    simp only [growthTotal,lossTotal,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [Pi.smul_apply,smul_eq_mul,perturbedField,Sum.elim_inr,
    ← Finset.mul_sum,hi,total] using hh

theorem perturbed_extension_abundance_bound {n : ℕ} (r : Rates n) (Q : ℝ)
    (hk : ∀ i, r.k i ≤ 2) (hm : ∀ i, 0 ≤ r.mu i) (hrho : ∀ i, (n:ℝ)/2 ≤ r.rho i)
    (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hz : ∀ t, 0 ≤ t → 4*X t (.inl 2) ≤ Q)
    (h0 : total (fun i => X 0 (.inr i)) ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • perturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → total (fun i => X t (.inr i)) ≤ Q := by
  apply scalar_upper_barrier _
    (fun t => b (X t)*(growthTotal r (X t (.inl 2)) (fun i => X t (.inr i))-
      lossTotal r (fun i => X t (.inr i)))) Q
    (fun t ht => perturbed_extension_aggregate_deriv r b X t (hd t ht)) h0
  intro t ht hq
  apply mul_nonpos_of_nonneg_of_nonpos (hb _)
  have hx := fun i => hX t ht (.inr i)
  have hs := total_nonneg (fun i => X t (.inr i)) hx
  have hl := weighted_loss_lower (fun i => X t (.inr i)) r.rho hx hrho
  have hc (i : Fin n) : r.k i*X t (.inl 2)-r.mu i ≤ 2*X t (.inl 2) := by
    have hh := mul_le_mul_of_nonneg_right (hk i) (hX t ht (.inl 2))
    linarith only [hh,hm i]
  have hg := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hc i) (hx i))
  have hg' : growthTotal r (X t (.inl 2)) (fun i => X t (.inr i)) ≤
      2*X t (.inl 2)*total (fun i => X t (.inr i)) := by
    simpa only [growthTotal,total,mul_comm,← Finset.mul_sum] using hg
  have hzs := mul_le_mul_of_nonneg_right ((hz t ht).trans hq) hs
  change (total (fun i => X t (.inr i)))^2/2 ≤ lossTotal r (fun i => X t (.inr i)) at hl
  nlinarith only [hl,hg',hzs]

theorem perturbed_field_linear_lower {n : ℕ} (r : Rates n) (hr : RateBox (baseRates r))
    (hk : ∀ i, 0 ≤ r.k i ∧ r.k i ≤ 2) (hm : ∀ i, r.mu i ≤ 1)
    (hrho : ∀ i, r.rho i ≤ (n:ℝ)+1)
    (R : ℝ) (hR : 1 ≤ R) (y : Vector n) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (hS : total (fun i => y (.inr i)) ≤ R) (i : Fin 4 ⊕ Fin n) :
    -(30+(21+(n:ℝ))*R)*y i ≤ perturbedField r y i := by
  cases i with
  | inl i =>
    have hu : ∀ j, rateDonorVector r y j ≤ 2*R := by
      intro j
      fin_cases j
      · change y (.inl 0) ≤ 2*R
        linarith [hy' (.inl 0)]
      · change y (.inl 1) ≤ 2*R
        linarith [hy' (.inl 1)]
      · change y (.inl 2) ≤ 2*R
        linarith [hy' (.inl 2)]
      · change y (.inl 3) ≤ 2*R
        linarith [hy' (.inl 3)]
      · have hh := copying_load_le_twice r (fun i => y (.inr i))
          (fun i => (hk i).2) (fun i => hy (.inr i))
        change copyingLoad r (fun i => y (.inr i)) ≤ 2*R
        linarith only [hh,hS]
    have hh := rate_linear_lower (baseRates r) hr (2*R) (by linarith)
      (rateDonorVector r y) (rateDonorVector_nonneg r y (fun i => (hk i).1) hy) hu i.castSucc
    have heq : rateDonorVector r y i.castSucc = y (.inl i) := by fin_cases i <;> rfl
    rw [heq] at hh
    have hp : 0 ≤ ((n:ℝ)+1)*R*y (.inl i) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith)) (hy (.inl i))
    change -(30+(21+(n:ℝ))*R)*y (.inl i) ≤ rateField (baseRates r) (rateDonorVector r y) i.castSucc
    nlinarith only [hh,hp]
  | inr i =>
    have hx := hy (.inr i)
    have hprod := mul_nonneg (hk i).1 (mul_nonneg hx (hy (.inl 2)))
    have hmu := mul_le_mul_of_nonneg_right (hm i) hx
    have hloss := mul_le_mul_of_nonneg_right (hrho i) (sq_nonneg (y (.inr i)))
    have hxx : (y (.inr i))^2 ≤ R*y (.inr i) := by nlinarith [hy' (.inr i)]
    have hnxx := mul_le_mul_of_nonneg_left hxx (show 0 ≤ (n:ℝ)+1 by positivity)
    have hRx := mul_nonneg (show 0 ≤ R by linarith) hx
    change -(30+(21+(n:ℝ))*R)*y (.inr i) ≤
      y (.inr i)*(r.k i*y (.inl 2)-r.mu i-r.rho i*y (.inr i))
    nlinarith only [hx,hprod,hmu,hloss,hnxx,hRx]

end MultiConsumerPermanence

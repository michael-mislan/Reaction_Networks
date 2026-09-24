import proofs.MultiConsumerPermanence.ReservoirFlow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

theorem reservoir_extension_total_bound {n : ℕ} (e feed wash S : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hS : 34 ≤ S) (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 0)+X 0 (.inl 1) ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirField e feed wash (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fA (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2))+fB (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)))) S
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 0)).add ((hasDerivAt_pi.1 (hd t ht)) (.inl 1)) using 1
    dsimp [reservoirField,consumerField,reservoirDonorVector]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := total_upper_comparison (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) e (hX t ht (.inl 0)) he
    have hprod : (49999/50000:ℝ)*34 ≤ (1-e)*(X t (.inl 0)+X t (.inl 1)) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    linarith

theorem reservoir_extension_weighted_bound {n : ℕ} (e feed wash S W : ℝ) (hW : (7/2)*(S+76) ≤ W)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S)
    (h0 : X 0 (.inl 2)+(7/4:ℝ)*X 0 (.inl 3) ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirField e feed wash (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 2)+(7/4:ℝ)*X t (.inl 3) ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fZ (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3))-(X t (.inl 2))*(X t (.inl 4)*total (fun i => X t (.inr i)))+(7/4:ℝ)*fH (flagshipRates e) (X t (.inl 2)) (X t (.inl 3)))) W
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 2)).add (((hasDerivAt_pi.1 (hd t ht)) (.inl 3)).const_mul (7/4:ℝ)) using 1
    dsimp [reservoirField,consumerField,reservoirDonorVector]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := weighted_upper_comparison_general (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) e S
      (by have hh := hS t ht; have hh' := hX t ht (.inl 1); linarith)
      (hX t ht (.inl 1)) (hX t ht (.inl 2)) (hX t ht (.inl 3))
    have hfeed := mul_nonneg (hX t ht (.inl 2)) (mul_nonneg (hX t ht (.inl 4)) (total_nonneg _ (fun i => hX t ht (.inr i))))
    linarith


theorem reservoir_extension_aggregate_deriv {n : ℕ} (e feed wash : ℝ) (b : ReservoirVector n → ℝ)
    (X : ℝ → ReservoirVector n) (t : ℝ)
    (hd : HasDerivAt X (b (X t) • reservoirField e feed wash (X t)) t) :
    HasDerivAt (fun s => total (fun i => X s (.inr i)))
      (b (X t)*((X t (.inl 4)*X t (.inl 2)-1/2)*total (fun i => X t (.inr i))-
        (n:ℝ)*squares (fun i => X t (.inr i)))) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_pi.1 hd (.inr i))
  simpa only [Pi.smul_apply,smul_eq_mul,reservoirField,Sum.elim_inr,
    ← Finset.mul_sum,aggregate_identity,total] using hh


theorem reservoir_extension_supply_bound {n : ℕ} (e d c Q : ℝ)
    (hc : 0 < c) (hcd : c ≤ d) (hc' : c ≤ 1/2) (hQ : d/c ≤ Q)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 4)+total (fun i => X 0 (.inr i)) ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirField e d d (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 4)+total (fun i => X t (.inr i)) ≤ Q := by
  apply scalar_upper_barrier _ (fun t => b (X t)*(d-d*X t (.inl 4)-
    (1/2)*total (fun i => X t (.inr i))-(n:ℝ)*squares (fun i => X t (.inr i)))) Q ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 4)).add
      (reservoir_extension_aggregate_deriv e d d b X t (hd t ht)) using 1
    simp [reservoirField]
    ring
  · intro t ht hq
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hR := hX t ht (.inl 4)
    have hS := total_nonneg (fun i => X t (.inr i)) (fun i => hX t ht (.inr i))
    have hQ' := (div_le_iff₀ hc).1 hQ
    have hsum := mul_le_mul_of_nonneg_left hq hc.le
    have hr := mul_le_mul_of_nonneg_right hcd hR
    have hs := mul_le_mul_of_nonneg_right hc' hS
    have hnq : 0 ≤ (n:ℝ)*squares (fun i => X t (.inr i)) :=
      mul_nonneg (Nat.cast_nonneg n) (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    nlinarith only [hQ',hsum,hr,hs,hnq]

theorem reservoir_coordinate_le_total {n : ℕ} (y : ReservoirVector n)
    (hy : ∀ i, 0 ≤ y i) (i : Fin n) :
    y (.inr i) ≤ total (fun j => y (.inr j)) := by
  exact Finset.single_le_sum (fun j _ => hy (.inr j)) (Finset.mem_univ i)

theorem reservoir_field_linear_lower {n : ℕ} (e d R : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hd : 0 ≤ d) (hR : 1 ≤ R)
    (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (hS : total (fun i => y (.inr i)) ≤ R) (i : Fin 5 ⊕ Fin n) :
    -(31+d+((n:ℝ)+11)*R^2)*y i ≤ reservoirField e d d y i := by
  have hRR : R ≤ R^2 := by nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hload : y (.inl 4)*total (fun i => y (.inr i)) ≤ R^2 := by
    have hh := mul_le_mul (hy' (.inl 4)) hS
      (total_nonneg _ (fun i => hy (.inr i))) hR0
    nlinarith only [hh]
  have hu : ∀ j, reservoirDonorVector y j ≤ R^2 := by
    intro j
    fin_cases j
    · exact (hy' (.inl 0)).trans hRR
    · exact (hy' (.inl 1)).trans hRR
    · exact (hy' (.inl 2)).trans hRR
    · exact (hy' (.inl 3)).trans hRR
    · exact hload
  have hcoef : 20+7*R^2 ≤ 31+d+((n:ℝ)+11)*R^2 := by
    have hh := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg R)
    nlinarith only [hh,hd,sq_nonneg R]
  cases i with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      have hzS := mul_le_mul (hy' (.inl 2)) hS
        (total_nonneg _ (fun i => hy (.inr i))) hR0
      have hzSR := mul_le_mul_of_nonneg_right hzS (hy (.inl 4))
      have hrest : 0 ≤ (31+((n:ℝ)+10)*R^2)*y (.inl 4) :=
        mul_nonneg (by positivity) (hy (.inl 4))
      simp [reservoirField]
      nlinarith only [hzSR,hrest,hd]
    · have hh := consumer_linear_lower e (R^2) he he' (by nlinarith)
        (reservoirDonorVector y) (reservoirDonorVector_nonneg y hy) hu i
      have heq : reservoirDonorVector y i = y (.inl i) := by
        fin_cases i <;> simp_all [reservoirDonorVector]
      rw [heq] at hh
      have hc := mul_le_mul_of_nonneg_right hcoef (hy (.inl i))
      simp only [reservoirField,Sum.elim_inl,if_neg hi]
      nlinarith only [hh,hc]
  | inr i =>
    have hx := hy (.inr i)
    have hprod := mul_nonneg hx (mul_nonneg (hy (.inl 4)) (hy (.inl 2)))
    have hxx : (y (.inr i))^2 ≤ R^2*y (.inr i) := by
      have hh := mul_le_mul_of_nonneg_right ((hy' (.inr i)).trans hRR) hx
      nlinarith only [hh]
    have hnxx := mul_le_mul_of_nonneg_left hxx (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hdx := mul_nonneg hd hx
    have hRx := mul_nonneg (sq_nonneg R) hx
    simp only [reservoirField,Sum.elim_inr]
    nlinarith only [hx,hprod,hnxx,hdx,hRx]

end MultiConsumerPermanence

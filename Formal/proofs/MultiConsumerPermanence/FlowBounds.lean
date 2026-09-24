import proofs.MultiConsumerPermanence.Flow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

theorem extension_total_bound {n : ℕ} (e S : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hS : 34 ≤ S) (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 0)+X 0 (.inl 1) ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field e (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fA (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2))+fB (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)))) S
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 0)).add ((hasDerivAt_pi.1 (hd t ht)) (.inl 1)) using 1
    dsimp [field,consumerField,donorVector]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := total_upper_comparison (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) e (hX t ht (.inl 0)) he
    have hprod : (49999/50000:ℝ)*34 ≤ (1-e)*(X t (.inl 0)+X t (.inl 1)) :=
      mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
    linarith

theorem extension_weighted_bound {n : ℕ} (e S W : ℝ) (hW : (7/2)*(S+76) ≤ W)
    (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S)
    (h0 : X 0 (.inl 2)+(7/4:ℝ)*X 0 (.inl 3) ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field e (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 2)+(7/4:ℝ)*X t (.inl 3) ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (fZ (flagshipRates e) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3))-(X t (.inl 2))*(total (fun i => X t (.inr i)))+(7/4:ℝ)*fH (flagshipRates e) (X t (.inl 2)) (X t (.inl 3)))) W
    ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 2)).add (((hasDerivAt_pi.1 (hd t ht)) (.inl 3)).const_mul (7/4:ℝ)) using 1
    dsimp [field,consumerField,donorVector]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := weighted_upper_comparison_general (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) e S
      (by have hh := hS t ht; have hh' := hX t ht (.inl 1); linarith)
      (hX t ht (.inl 1)) (hX t ht (.inl 2)) (hX t ht (.inl 3))
    have hfeed := mul_nonneg (hX t ht (.inl 2)) (total_nonneg _ (fun i => hX t ht (.inr i)))
    linarith


theorem extension_aggregate_deriv {n : ℕ} (e : ℝ) (b : Vector n → ℝ)
    (X : ℝ → Vector n) (t : ℝ)
    (hd : HasDerivAt X (b (X t) • field e (X t)) t) :
    HasDerivAt (fun s => total (fun i => X s (.inr i)))
      (b (X t)*((X t (.inl 2)-1/2)*total (fun i => X t (.inr i))-
        (n:ℝ)*squares (fun i => X t (.inr i)))) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_pi.1 hd (.inr i))
  simpa only [Pi.smul_apply,smul_eq_mul,field,Sum.elim_inr,
    ← Finset.mul_sum,aggregate_identity,total] using hh

theorem extension_abundance_bound {n : ℕ} (e Q : ℝ)
    (b : Vector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → Vector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hz : ∀ t, 0 ≤ t → X t (.inl 2) ≤ Q)
    (h0 : total (fun i => X 0 (.inr i)) ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • field e (X t)) t) :
    ∀ t, 0 ≤ t → total (fun i => X t (.inr i)) ≤ Q := by
  apply scalar_upper_barrier (fun t => total (fun i => X t (.inr i)))
    (fun t => b (X t)*((X t (.inl 2)-1/2)*total (fun i => X t (.inr i))-
      (n:ℝ)*squares (fun i => X t (.inr i)))) Q
    (fun t ht => extension_aggregate_deriv e b X t (hd t ht)) h0
  intro t ht hq
  apply mul_nonpos_of_nonneg_of_nonpos (hb _)
  have hx := total_nonneg (fun i => X t (.inr i)) (fun i => hX t ht (.inr i))
  have hc := (squares_bounds (fun i => X t (.inr i)) (fun i => hX t ht (.inr i))).2
  have hh := mul_le_mul_of_nonneg_right ((hz t ht).trans hq) hx
  nlinarith only [hc,hh,hx]

theorem coordinate_le_total {n : ℕ} (y : Vector n) (hy : ∀ i, 0 ≤ y i) (i : Fin n) :
    y (.inr i) ≤ total (fun j => y (.inr j)) := by
  exact Finset.single_le_sum (fun j _ => hy (.inr j)) (Finset.mem_univ i)

theorem field_linear_lower {n : ℕ} (e R : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (hR : 1 ≤ R) (y : Vector n) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (hS : total (fun i => y (.inr i)) ≤ R) (i : Fin 4 ⊕ Fin n) :
    -(20+(7+(n:ℝ))*R)*y i ≤ field e y i := by
  cases i with
  | inl i =>
    have hu : ∀ j, donorVector y j ≤ R := by
      intro j
      fin_cases j
      · exact hy' (.inl 0)
      · exact hy' (.inl 1)
      · exact hy' (.inl 2)
      · exact hy' (.inl 3)
      · exact hS
    have hh := consumer_linear_lower e R he he' hR (donorVector y)
      (donorVector_nonneg y hy) hu i.castSucc
    have heq : donorVector y i.castSucc = y (.inl i) := by fin_cases i <;> rfl
    rw [heq] at hh
    have hp : 0 ≤ (n:ℝ)*R*y (.inl i) := mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (by linarith)) (hy _)
    change -(20+(7+(n:ℝ))*R)*y (.inl i) ≤ consumerField e (donorVector y) i.castSucc
    nlinarith only [hh,hp]
  | inr i =>
    have hx := hy (.inr i)
    have hxx := mul_le_mul_of_nonneg_left (hy' (.inr i)) hx
    have hnxx := mul_le_mul_of_nonneg_left hxx (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hzx := mul_nonneg (hy (.inl 2)) hx
    have hRx := mul_nonneg (by linarith : 0 ≤ R) hx
    change -(20+(7+(n:ℝ))*R)*y (.inr i) ≤ y (.inr i)*(y (.inl 2)-1/2-(n:ℝ)*y (.inr i))
    nlinarith only [hx,hnxx,hzx,hRx]

end MultiConsumerPermanence

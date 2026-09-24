import proofs.MultiConsumerPermanence.ReservoirRateFlow

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence
open scoped BigOperators

theorem reservoir_rate_extension_total_bound {n : ℕ} (r : ReservoirRates n) (hr : RateBox (baseRates r.reactions)) (S : ℝ)
    (hS : 34 ≤ S) (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 0)+X 0 (.inl 1) ≤ S)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirPerturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateA (baseRates r.reactions) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2))+rateB (baseRates r.reactions) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)))) S ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 0)).add ((hasDerivAt_pi.1 (hd t ht)) (.inl 1)) using 1
    dsimp [reservoirPerturbedField,rateField,reservoirRateDonorVector]
    ring
  · intro t ht hs
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_total_upper (baseRates r.reactions) hr (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (hX t ht (.inl 0)) (hX t ht (.inl 1))
    linarith only [hh,hs,hS]

theorem reservoir_rate_extension_weighted_bound {n : ℕ} (r : ReservoirRates n) (hr : RateBox (baseRates r.reactions))
    (hk : ∀ i, 0 ≤ r.reactions.k i) (S W : ℝ)
    (hW : (7/2)*(2*S+200) ≤ W) (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (hS : ∀ t, 0 ≤ t → X t (.inl 0)+X t (.inl 1) ≤ S) (h0 : X 0 (.inl 2)+(7/4:ℝ)*X 0 (.inl 3) ≤ W)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirPerturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 2)+(7/4:ℝ)*X t (.inl 3) ≤ W := by
  apply scalar_upper_barrier _ (fun t => b (X t)*
    (rateZ (baseRates r.reactions) (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) (X t (.inl 4)*copyingLoad r.reactions (fun i => X t (.inr i)))+(7/4:ℝ)*rateH (baseRates r.reactions) (X t (.inl 2)) (X t (.inl 3)))) W ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 2)).add (((hasDerivAt_pi.1 (hd t ht)) (.inl 3)).const_mul (7/4:ℝ)) using 1
    dsimp [reservoirPerturbedField,rateField,reservoirRateDonorVector]
    ring
  · intro t ht hw
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hh := rate_weighted_general (baseRates r.reactions) hr (X t (.inl 0)) (X t (.inl 1)) (X t (.inl 2)) (X t (.inl 3)) (X t (.inl 4)*copyingLoad r.reactions (fun i => X t (.inr i))) S
      (hX t ht (.inl 0)) (by have hh := hS t ht; have hn := hX t ht (.inl 1); linarith)
      (hX t ht (.inl 1)) (hX t ht (.inl 2)) (hX t ht (.inl 3)) (mul_nonneg (hX t ht (.inl 4)) (copying_load_nonneg r.reactions _ hk (fun i => hX t ht (.inr i))))
    linarith only [hh,hw,hW]



noncomputable def maintenanceTotal {n : ℕ} (r : Rates n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, r.mu i*x i

theorem growth_total_split {n : ℕ} (r : Rates n) (z : ℝ) (x : Fin n → ℝ) :
    growthTotal r z x = z*copyingLoad r x-maintenanceTotal r x := by
  simp only [growthTotal,copyingLoad,maintenanceTotal,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem reservoir_rate_extension_aggregate_deriv {n : ℕ} (r : ReservoirRates n)
    (b : ReservoirVector n → ℝ) (X : ℝ → ReservoirVector n) (t : ℝ)
    (hd : HasDerivAt X (b (X t) • reservoirPerturbedField r (X t)) t) :
    HasDerivAt (fun s => total (fun i => X s (.inr i)))
      (b (X t)*(growthTotal r.reactions (X t (.inl 4)*X t (.inl 2)) (fun i => X t (.inr i))-
        lossTotal r.reactions (fun i => X t (.inr i)))) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_pi.1 hd (.inr i))
  have hi : (∑ i, X t (.inr i)*(r.reactions.k i*(X t (.inl 4)*X t (.inl 2))-
      r.reactions.mu i-r.reactions.rho i*X t (.inr i))) =
      growthTotal r.reactions (X t (.inl 4)*X t (.inl 2)) (fun i => X t (.inr i))-
        lossTotal r.reactions (fun i => X t (.inr i)) := by
    simp only [growthTotal,lossTotal,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [Pi.smul_apply,smul_eq_mul,reservoirPerturbedField,Sum.elim_inr,
    ← Finset.mul_sum,hi,total] using hh

theorem reservoir_rate_extension_supply_bound {n : ℕ} (r : ReservoirRates n) (c Q : ℝ)
    (hc : 0 < c) (hcw : c ≤ r.wash) (hm : ∀ i, c ≤ r.reactions.mu i)
    (hrho : ∀ i, 0 ≤ r.reactions.rho i) (hQ : r.feed/c ≤ Q)
    (b : ReservoirVector n → ℝ) (hb : ∀ x, 0 ≤ b x)
    (X : ℝ → ReservoirVector n) (hX : ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i)
    (h0 : X 0 (.inl 4)+total (fun i => X 0 (.inr i)) ≤ Q)
    (hd : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • reservoirPerturbedField r (X t)) t) :
    ∀ t, 0 ≤ t → X t (.inl 4)+total (fun i => X t (.inr i)) ≤ Q := by
  apply scalar_upper_barrier _ (fun t => b (X t)*(r.feed-r.wash*X t (.inl 4)-
    maintenanceTotal r.reactions (fun i => X t (.inr i))-
    lossTotal r.reactions (fun i => X t (.inr i)))) Q ?_ h0 ?_
  · intro t ht
    convert ((hasDerivAt_pi.1 (hd t ht)) (.inl 4)).add
      (reservoir_rate_extension_aggregate_deriv r b X t (hd t ht)) using 1
    simp [reservoirPerturbedField,growth_total_split]
    ring
  · intro t ht hq
    apply mul_nonpos_of_nonneg_of_nonpos (hb _)
    have hR := hX t ht (.inl 4)
    have hQ' := (div_le_iff₀ hc).1 hQ
    have hsum := mul_le_mul_of_nonneg_left hq hc.le
    have hr := mul_le_mul_of_nonneg_right hcw hR
    have hs : c*total (fun i => X t (.inr i)) ≤ maintenanceTotal r.reactions (fun i => X t (.inr i)) := by
      have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
        mul_le_mul_of_nonneg_right (hm i) (hX t ht (.inr i)))
      simpa only [maintenanceTotal,total,Finset.mul_sum] using hh
    have hl : 0 ≤ lossTotal r.reactions (fun i => X t (.inr i)) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hrho i) (sq_nonneg _))
    nlinarith only [hQ',hsum,hr,hs,hl]

theorem reservoir_rate_field_linear_lower {n : ℕ} (r : ReservoirRates n)
    (hr : RateBox (baseRates r.reactions)) (hk : ∀ i, 0 ≤ r.reactions.k i ∧ r.reactions.k i ≤ 2)
    (hm : ∀ i, r.reactions.mu i ≤ 1) (hrho : ∀ i, r.reactions.rho i ≤ (n:ℝ)+1)
    (hf : 0 ≤ r.feed) (hw : 0 ≤ r.wash) (R : ℝ) (hR : 1 ≤ R)
    (y : ReservoirVector n) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (hS : total (fun i => y (.inr i)) ≤ R) (i : Fin 5 ⊕ Fin n) :
    -(31+r.wash+((n:ℝ)+21)*R^2)*y i ≤ reservoirPerturbedField r y i := by
  have hRR : R ≤ R^2 := by nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hK := copying_load_le_twice r.reactions (fun i => y (.inr i))
    (fun i => (hk i).2) (fun i => hy (.inr i))
  have hK' : copyingLoad r.reactions (fun i => y (.inr i)) ≤ 2*R := by linarith only [hK,hS]
  have hload := mul_le_mul (hy' (.inl 4)) hK'
    (copying_load_nonneg _ _ (fun i => (hk i).1) (fun i => hy (.inr i))) hR0
  have hu : ∀ j, reservoirRateDonorVector r y j ≤ 2*R^2 := by
    intro j
    fin_cases j
    · change y (.inl 0) ≤ 2*R^2
      nlinarith only [hy' (.inl 0),hRR,sq_nonneg R]
    · change y (.inl 1) ≤ 2*R^2
      nlinarith only [hy' (.inl 1),hRR,sq_nonneg R]
    · change y (.inl 2) ≤ 2*R^2
      nlinarith only [hy' (.inl 2),hRR,sq_nonneg R]
    · change y (.inl 3) ≤ 2*R^2
      nlinarith only [hy' (.inl 3),hRR,sq_nonneg R]
    · change y (.inl 4)*copyingLoad r.reactions (fun i => y (.inr i)) ≤ 2*R^2
      nlinarith only [hload]
  have hcoef : 30+20*R^2 ≤ 31+r.wash+((n:ℝ)+21)*R^2 := by
    have hh := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg R)
    nlinarith only [hh,hw,sq_nonneg R]
  cases i with
  | inl i =>
    by_cases hi : i = 4
    · subst i
      have hzK := mul_le_mul (hy' (.inl 2)) hK'
        (copying_load_nonneg _ _ (fun i => (hk i).1) (fun i => hy (.inr i))) hR0
      have hzKR := mul_le_mul_of_nonneg_right hzK (hy (.inl 4))
      have hrest : 0 ≤ (31+((n:ℝ)+19)*R^2)*y (.inl 4) :=
        mul_nonneg (by positivity) (hy (.inl 4))
      simp [reservoirPerturbedField]
      nlinarith only [hzKR,hrest,hf]
    · have hh := rate_linear_lower (baseRates r.reactions) hr (2*R^2) (by nlinarith)
        (reservoirRateDonorVector r y) (reservoirRateDonorVector_nonneg r (fun i => (hk i).1) y hy) hu i
      have heq : reservoirRateDonorVector r y i = y (.inl i) := by
        fin_cases i <;> simp_all [reservoirRateDonorVector]
      rw [heq] at hh
      have hc := mul_le_mul_of_nonneg_right hcoef (hy (.inl i))
      simp only [reservoirPerturbedField,Sum.elim_inl,if_neg hi]
      nlinarith only [hh,hc]
  | inr i =>
    have hx := hy (.inr i)
    have hprod := mul_nonneg (hk i).1 (mul_nonneg hx (mul_nonneg (hy (.inl 4)) (hy (.inl 2))))
    have hmu := mul_le_mul_of_nonneg_right (hm i) hx
    have hloss := mul_le_mul_of_nonneg_right (hrho i) (sq_nonneg (y (.inr i)))
    have hxx : (y (.inr i))^2 ≤ R^2*y (.inr i) := by
      have hh := mul_le_mul_of_nonneg_right ((hy' (.inr i)).trans hRR) hx
      nlinarith only [hh]
    have hnxx := mul_le_mul_of_nonneg_left hxx (show 0 ≤ (n:ℝ)+1 by positivity)
    have hwx := mul_nonneg hw hx
    have hRx := mul_nonneg (sq_nonneg R) hx
    simp only [reservoirPerturbedField,Sum.elim_inr]
    nlinarith only [hx,hprod,hmu,hloss,hnxx,hwx,hRx]

end MultiConsumerPermanence

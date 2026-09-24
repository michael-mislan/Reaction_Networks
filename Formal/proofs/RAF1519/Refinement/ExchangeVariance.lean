import proofs.RAF1519.Refinement.CountVariance

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators

def exchangeSupport {n : ℕ} (p : Fin n × Fin 7) (i j : Fin n) (s : Fin 7) : ℝ :=
  (if p=(i,s) then 1 else 0)+(if p=(j,s) then 1 else 0)

theorem exchange_support_nonnegative {n : ℕ} (p : Fin n × Fin 7) (i j : Fin n) (s : Fin 7) :
    0 ≤ exchangeSupport p i j s := by unfold exchangeSupport; positivity

theorem exchange_increment_square {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : 0 < V)
    (p : Fin n × Fin 7) (N : MolecularState n) (i j : Fin n) (s : Fin 7) :
    (molecularIncrement r d k V p N (.inr (i,j,s)))^2 ≤
      (2/V)^2*exchangeSupport p i j s := by
  have hb := molecular_increment_square r d k V hV p N (.inr (i,j,s))
  by_cases hi : p=(i,s) <;> by_cases hj : p=(j,s)
  · simp only [exchangeSupport,if_pos hi,if_pos hj]
    nlinarith [sq_nonneg (2/V)]
  · simpa only [exchangeSupport,if_pos hi,if_neg hj,add_zero,mul_one] using hb
  · simpa only [exchangeSupport,if_neg hi,if_pos hj,zero_add,mul_one] using hb
  · rw [exchange_increment_off_nodes r d k V N p i j s hi hj]
    simp [exchangeSupport,hi,hj]

theorem exchange_variance_term {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ) (hV : 0 < V) (hk : ∀ i j, 0 ≤ k i j)
    (p : Fin n × Fin 7) (N : MolecularState n) (hN : ∀ q, (N q:ℝ)/V ≤ 11/10)
    (i j : Fin n) (s : Fin 7) :
    molecularRate r d k V N (.inr (i,j,s))*(molecularIncrement r d k V p N (.inr (i,j,s)))^2 ≤
      (22/(5*V))*k i j*exchangeSupport p i j s := by
  have hrate : molecularRate r d k V N (.inr (i,j,s)) ≤ k i j*((11/10)*V) := by
    rw [exchange_rate r d k V (ne_of_gt hV)]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hV).mp (hN (i,s))) (hk i j)
  have hr0 : 0 ≤ molecularRate r d k V N (.inr (i,j,s)) := by
    rw [exchange_rate r d k V (ne_of_gt hV)]
    exact mul_nonneg (hk i j) (Nat.cast_nonneg _)
  calc
    _ ≤ molecularRate r d k V N (.inr (i,j,s))*((2/V)^2*exchangeSupport p i j s) :=
      mul_le_mul_of_nonneg_left (exchange_increment_square r d k V hV p N i j s) hr0
    _ ≤ (k i j*((11/10)*V))*((2/V)^2*exchangeSupport p i j s) :=
      mul_le_mul_of_nonneg_right hrate (mul_nonneg (sq_nonneg _) (exchange_support_nonnegative p i j s))
    _ = _ := by field_simp; ring

theorem exchange_support_sum {n : ℕ} (k : Fin n → Fin n → ℝ) (u : Fin n) (t : Fin 7) :
    (∑ a : Fin n × Fin n × Fin 7, k a.1 a.2.1*exchangeSupport (u,t) a.1 a.2.1 a.2.2) =
      (∑ j, k u j)+(∑ i, k i u) := by
  simp only [Fintype.sum_prod_type,exchangeSupport,mul_add,Finset.sum_add_distrib]
  simp [Prod.mk.injEq,ite_and,mul_ite,Finset.sum_ite_irrel]

theorem exchange_coordinate_variance {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hk : ∀ i j, 0 ≤ k i j)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (p : Fin n × Fin 7) (N : MolecularState n) (hN : ∀ q, (N q:ℝ)/V ≤ 11/10) :
    (∑ a : Fin n × Fin n × Fin 7, molecularRate r d k V N (.inr a)*
      (molecularIncrement r d k V p N (.inr a))^2) ≤ (22/(5*V))*(2*Δ) := by
  have hcol : (∑ i, k i p.1) ≤ Δ := by
    calc
      _ = ∑ i, k p.1 i := Finset.sum_congr rfl (fun i _ => hsym i p.1)
      _ ≤ _ := hdegree p.1
  calc
    _ ≤ ∑ a : Fin n × Fin n × Fin 7, (22/(5*V))*k a.1 a.2.1*exchangeSupport p a.1 a.2.1 a.2.2 :=
      Finset.sum_le_sum (fun a _ => exchange_variance_term r d k V hV hk p N hN a.1 a.2.1 a.2.2)
    _ = (22/(5*V))*((∑ j, k p.1 j)+(∑ i, k i p.1)) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      exact exchange_support_sum k p.1 p.2
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hdegree p.1]) (by positivity)

theorem molecular_coordinate_variance {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (p : Fin n × Fin 7) (N : MolecularState n) (hN : ∀ q, (N q:ℝ)/V ≤ 11/10) :
    (∑ a, molecularRate r d k V N a*(molecularIncrement r d k V p N a)^2) ≤
      800*(1+Δ)/V := by
  rw [Fintype.sum_sum_type]
  have hb := add_le_add (local_coordinate_variance r d k V hr hd hk hV p N hN)
    (exchange_coordinate_variance r d k V Δ hV hk hsym hdegree p N hN)
  apply hb.trans
  have he : 800/V+(22/(5*V))*(2*Δ) = 800/V+(44/5)*(Δ/V) := by ring
  rw [he]
  have hq : 0 ≤ Δ/V := div_nonneg hΔ hV.le
  have he' : 800*(1+Δ)/V = 800/V+800*(Δ/V) := by ring
  rw [he']
  linarith

end
end RAF1519.Refinement

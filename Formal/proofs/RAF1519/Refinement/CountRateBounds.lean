import proofs.RAF1519.Refinement.CountLocality

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def forwardBound (j : Fin 7) : ℝ := match j.val with
  | 0 => (1/500000000)*(11/10)^2
  | 1 => 20*(11/10)^2
  | 2 => 20*(11/10)^2
  | 3 => 20*(11/10)
  | 4 => 21*(11/10)
  | 5 => (1/25)*(101/100)*(11/10)
  | _ => 100*(1/25)*(11/10)

def reverseBound (j : Fin 7) : ℝ := match j.val with
  | 0 => (1/5000000000)*(11/10)
  | 1 => 20*(11/10)
  | 2 => 20*(11/10)
  | 3 => 2*(11/10)
  | 4 => 21*(11/10)^2
  | 5 => (1/25)*(11/10)
  | _ => (1/25)*(101/8000000000)*(11/10)^2

theorem forward_rate_bound (r d : ℝ) (hr : 0 ≤ r ∧ r ≤ 21) (hd : 0 ≤ d ∧ d ≤ 1/25)
    (c : State) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 11/10) (j : Fin 7) :
    forwardRate r d (1/100) (1/100) c j ≤ forwardBound j := by
  have hp (i j : Fin 7) : c i*c j ≤ (11/10:ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul (hc i).2 (hc j).2 (hc j).1 (by norm_num : (0:ℝ) ≤ 11/10)
  have hD (i : Fin 7) : d*c i ≤ (1/25:ℝ)*(11/10) :=
    mul_le_mul hd.2 (hc i).2 (hc i).1 (by norm_num)
  have hR (i : Fin 7) : r*c i ≤ 21*(11/10:ℝ) :=
    mul_le_mul hr.2 (hc i).2 (hc i).1 (by norm_num)
  fin_cases j <;> norm_num [forwardRate,forwardBound]
  · nlinarith [hp 0 1]
  · nlinarith [hp 2 0]
  · nlinarith [hp 3 1]
  · linarith [(hc 4).2]
  · linarith [hR 5]
  · nlinarith [hD 2]
  · nlinarith [hD 6]

theorem reverse_rate_bound (r d V : ℝ) (hr : 0 ≤ r ∧ r ≤ 21) (hd : 0 ≤ d ∧ d ≤ 1/25)
    (hV : 0 < V) (c : State) (hc : ∀ i, 0 ≤ c i ∧ c i ≤ 11/10) (j : Fin 7) :
    reverseRate r d (1/100) (1/100) V c j ≤ reverseBound j := by
  have hp : c 0*c 1 ≤ (11/10:ℝ)^2 := by
    simpa only [pow_two] using mul_le_mul (hc 0).2 (hc 1).2 (hc 1).1 (by norm_num : (0:ℝ) ≤ 11/10)
  have hD : d*c 6 ≤ (1/25:ℝ)*(11/10) :=
    mul_le_mul hd.2 (hc 6).2 (hc 6).1 (by norm_num)
  have hDuw : d*(c 0*c 1) ≤ (1/25:ℝ)*(11/10)^2 :=
    mul_le_mul hd.2 hp (mul_nonneg (hc 0).1 (hc 1).1) (by norm_num)
  have hsq : (c 2)^2 ≤ (11/10:ℝ)^2 := (sq_le_sq₀ (hc 2).1 (by norm_num)).mpr (hc 2).2
  have hR : r*((c 2)^2-c 2/V) ≤ 21*(11/10:ℝ)^2 :=
    (mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg (hc 2).1 hV.le)) hr.1).trans
      (mul_le_mul hr.2 hsq (sq_nonneg _) (by norm_num))
  fin_cases j <;> norm_num [reverseRate,reverseBound]
  · linarith [(hc 2).2]
  · linarith [(hc 3).2]
  · linarith [(hc 4).2]
  · linarith [(hc 5).2]
  · linarith [hR]
  · linarith [hD]
  · nlinarith [hDuw]

theorem local_total_rate_bound (r d V : ℝ) (hr : 0 ≤ r ∧ r ≤ 21) (hd : 0 ≤ d ∧ d ≤ 1/25)
    (hV : 0 < V) (N : Fin 7 → ℕ) (hN : ∀ i, (N i:ℝ)/V ≤ 11/10) :
    (∑ a, (localReaction r d a).rate V N) ≤ 200*V := by
  have hc : ∀ i, 0 ≤ concentration V N i ∧ concentration V N i ≤ 11/10 :=
    fun i => ⟨div_nonneg (Nat.cast_nonneg _) hV.le,hN i⟩
  have hf (j : Fin 7) : (localReaction r d (.inl (j,false))).rate V N ≤ V*forwardBound j := by
    rw [local_forward_binding r d V (ne_of_gt hV)]
    exact mul_le_mul_of_nonneg_left (forward_rate_bound r d hr hd _ hc j) hV.le
  have hb (j : Fin 7) : (localReaction r d (.inl (j,true))).rate V N ≤ V*reverseBound j := by
    rw [local_reverse_binding r d V (ne_of_gt hV)]
    exact mul_le_mul_of_nonneg_left (reverse_rate_bound r d V hr hd hV _ hc j) hV.le
  have hw (j : Fin 7) : (localReaction r d (.inr (.inr j))).rate V N ≤ V*(11/10) := by
    rw [local_wash_rate r d V (ne_of_gt hV)]
    have h := (div_le_iff₀ hV).mp (hN j)
    linarith
  have hs : (∑ a, (localReaction r d a).rate V N) ≤
      (∑ j, (V*forwardBound j+V*reverseBound j))+(2*V+7*(V*(11/10))) := by
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
      local_food_rate,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j _
      linarith [hf j,hb j]
    · apply add_le_add le_rfl
      calc
        _ ≤ ∑ j : Fin 7, V*(11/10) := Finset.sum_le_sum (fun j _ => hw j)
        _ = _ := by simp
  have he : (∑ j, (V*forwardBound j+V*reverseBound j))+(2*V+7*(V*(11/10))) =
      (3585968800065021/20000000000000:ℝ)*V := by
    norm_num [forwardBound,reverseBound,Fin.sum_univ_succ]
    ring
  rw [he] at hs
  nlinarith

end
end RAF1519.Refinement

import proofs.HeritableCompositions.PartitionProduct

namespace HeritableCompositions

theorem weighted_union_bound {ι α : Type*} [Fintype ι] (S : Finset α)
    (w : α → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x) (A : ι → α → Prop)
    [∀ i, DecidablePred (A i)] [∀ x, Decidable (∃ i, A i x)] :
    (∑ x ∈ S, w x*(if ∃ i, A i x then 1 else 0)) ≤
      ∑ i, ∑ x ∈ S, w x*(if A i x then 1 else 0) := by
  classical
  have hpoint (x : α) (hx : x ∈ S) : w x*(if ∃ i, A i x then 1 else 0) ≤
      ∑ i, w x*(if A i x then 1 else 0) := by
    by_cases ha : ∃ i, A i x
    · obtain ⟨j,hj⟩ := ha
      have hh : w x*(if A j x then 1 else 0) ≤ ∑ i, w x*(if A i x then 1 else 0) := Finset.single_le_sum
        (f := fun i => w x*(if A i x then 1 else 0))
        (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hw x hx) (by split_ifs <;> norm_num))
        (Finset.mem_univ j)
      have hex : ∃ i, A i x := ⟨j,hj⟩
      simpa only [if_pos hex,if_pos hj,mul_one] using hh
    · simp only [if_neg ha,mul_zero]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw x hx) (by split_ifs <;> norm_num))
  have h := Finset.sum_le_sum (fun x hx => hpoint x hx)
  rw [Finset.sum_comm] at h
  exact h

theorem binomial_volume_tail (n N : ℕ) (hN : 0 < N) (hn : (n : ℝ) ≤ 70*(N : ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    (∑ k ∈ Finset.range (n+1), if (N : ℝ)*δ ≤ |(k : ℝ)-(n : ℝ)/2| then fairBinomialWeight n k else 0) ≤
      2*Real.exp (-(N : ℝ)*δ^2/35) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hn0 : n=0
  · subst n
    have hd : ¬ (N : ℝ)*δ ≤ 0 := not_le.mpr (mul_pos hNr hδ)
    simp [hd]
    positivity
  · have hnr : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    have ht := fair_binomial_two_sided_tail n (Nat.pos_of_ne_zero hn0) ((N : ℝ)*δ) (by positivity)
    apply ht.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hnr).mpr
    have hh := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (N : ℝ)*δ^2)
    nlinarith only [hh]

theorem daughter_joint_tail (n : Fin 4 → ℕ) (N : ℕ) (hN : 0 < N)
    (hn : ∀ i, (n i : ℝ) ≤ 70*(N : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    (∑ d ∈ daughterDraws n, daughterWeight n d*
      (if ∃ i, (N : ℝ)*δ ≤ |(d i : ℝ)-(n i : ℝ)/2| then 1 else 0)) ≤
      8*Real.exp (-(N : ℝ)*δ^2/35) := by
  classical
  have h := weighted_union_bound (daughterDraws n) (daughterWeight n)
    (fun d _ => daughterWeight_nonneg n d) (fun i d => (N : ℝ)*δ ≤ |(d i : ℝ)-(n i : ℝ)/2|)
  have hm (i : Fin 4) :
      (∑ d ∈ daughterDraws n, daughterWeight n d*(if (N : ℝ)*δ ≤ |(d i : ℝ)-(n i : ℝ)/2| then 1 else 0)) ≤
        2*Real.exp (-(N : ℝ)*δ^2/35) := by
    rw [daughterWeight_marginal n i (fun k => if (N : ℝ)*δ ≤ |(k : ℝ)-(n i : ℝ)/2| then 1 else 0)]
    simpa only [mul_ite,mul_one,mul_zero] using binomial_volume_tail (n i) N hN (hn i) δ hδ
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hm i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hs
  apply h.trans
  convert hs using 1
  ring

end HeritableCompositions

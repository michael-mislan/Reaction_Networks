import proofs.SerialTransferSelection.CycleLaw

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

/-- A finite-family bound, proved without enumerating its inhabitants. -/
theorem exists_finite_family_bound {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) (k : ℝ) (hf : ∀ i x, 0 ≤ f i x) :
    ∃ q : NNReal, 0 < (q : ℝ) ∧ k ≤ q ∧ ∀ i x, f i x ≤ q := by
  classical
  let S : ℝ := ∑ i, ∑ x, f i x
  have hs : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun x _ => hf i x))
  have hq : 0 < 1+max k 0+S := by linarith [le_max_right k 0]
  refine ⟨⟨1+max k 0+S,hq.le⟩,hq,?_,?_⟩
  · change k ≤ 1+max k 0+S
    linarith [le_max_left k 0]
  · intro i x
    have hx : f i x ≤ ∑ y, f i y := Finset.single_le_sum (fun y _ => hf i y) (Finset.mem_univ x)
    have hi : (∑ y, f i y) ≤ S := by
      change (∑ y, f i y) ≤ ∑ j, ∑ y : α j, f j y
      exact Finset.single_le_sum (f := fun j => ∑ y : α j, f j y)
        (fun j _ => Finset.sum_nonneg (fun y _ => hf j y)) (Finset.mem_univ i)
    change f i x ≤ 1+max k 0+S
    linarith [le_max_right k 0]

theorem exists_uniform_source_clocks (N M : ℕ) (zL zH γ : ℝ) (hγ : 0 ≤ γ) (kb kr : ℝ) :
    ∃ qb qr : NNReal, 0 < (qb : ℝ) ∧ 0 < (qr : ℝ) ∧ kb ≤ qb ∧ kr ≤ qr ∧
      (∀ s : ReadyPopulation N M zL zH, ∀ x, (cycleBatchModel N M zL zH γ hγ s).total x ≤ qb) ∧
      ∀ tag x, (recoveryCellModel N zL zH tag).total x ≤ qr := by
  classical
  obtain ⟨qb,hqb,hkb,hb⟩ := exists_finite_family_bound
    (fun (s : ReadyPopulation N M zL zH) x => (cycleBatchModel N M zL zH γ hγ s).total x) kb
    (fun s x => Finset.sum_nonneg (fun r _ => (cycleBatchModel N M zL zH γ hγ s).nonneg x r))
  obtain ⟨qr,hqr,hkr,hr⟩ := exists_finite_family_bound
    (fun tag x => (recoveryCellModel N zL zH tag).total x) kr
    (fun tag x => Finset.sum_nonneg (fun r _ => (recoveryCellModel N zL zH tag).nonneg x r))
  exact ⟨qb,qr,hqb,hqr,hkb,hkr,hb,hr⟩

theorem exists_uniform_cycle_quotas (M : ℕ) (hM : 0 < M) (qb qr t δ : ℝ) (hδ : 0 < δ) :
    ∃ JB JR : ℕ, 0 < JB ∧ 0 < JR ∧ t*qb/JB < δ ∧ (M : ℝ)*(5376*qr/JR) < δ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨JB,hJB,hb⟩ := exists_finite_service_quota qb t δ hδ
  obtain ⟨JR,hJR,hr⟩ := exists_finite_service_quota qr 5376 (δ/(M : ℝ)) (div_pos hδ hMr)
  refine ⟨JB,JR,hJB,hJR,hb,?_⟩
  have hh := mul_lt_mul_of_pos_left hr hMr
  simpa only [mul_div_cancel₀ _ (ne_of_gt hMr)] using hh

end SerialTransferSelection

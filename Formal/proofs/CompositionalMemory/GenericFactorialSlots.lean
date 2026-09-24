import proofs.CompositionalMemory.GenericCountReaction
import proofs.CompositionalMemory.GenericPropensityBias

namespace CompositionalMemory

theorem descending_density_slots (n q : ℕ) (v : ℝ) :
    (n.descFactorial q:ℝ)/v^q = ∏ l : Fin q, ((n-l.val:ℕ):ℝ)/v := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun l : ℕ => ((n-l:ℕ):ℝ)) q]
  rw [Nat.descFactorial_eq_prod_range,Nat.cast_prod]

theorem count_reaction_density_slots {d : ℕ} (c v : ℝ) (consume n : Fin d → ℕ) :
    countReactionDensity c v consume n =
      c*(∏ j, ∏ l : Fin (consume j), ((n j-l.val:ℕ):ℝ)/v) := by
  simp_rw [← descending_density_slots]
  rw [Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
  unfold countReactionDensity
  ring

theorem count_reaction_density_bias {d : ℕ} (c v U : ℝ) (consume n : Fin d → ℕ)
    (hc : 0 ≤ c) (hv : 0 < v) (hU : 0 ≤ U) (hu : ∀ j, (n j:ℝ)/v ≤ U) :
    |countReactionDensity c v consume n-c*(∏ j, ((n j:ℝ)/v)^(consume j))| ≤
      c*(∑ j, consume j:ℕ)^2*(U+1)^(∑ j, consume j)/v := by
  let Slot := (j : Fin d) × Fin (consume j)
  have hoff (s : Slot) : s.2.val ≤ (Finset.univ : Finset Slot).card := by
    have hs : consume s.1 ≤ ∑ j, consume j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (consume j)) (Finset.mem_univ s.1)
    have ht := s.2.isLt
    simpa only [Slot,Finset.card_univ,Fintype.card_sigma,Fintype.card_fin] using
      (show s.2.val ≤ ∑ j, consume j by omega)
  have h := clipped_product_density_bias (Finset.univ : Finset Slot)
    (fun s => n s.1) (fun s => s.2.val) v U hv hU
    (fun s _ => hu s.1) (fun s _ => hoff s)
  dsimp only [Slot] at h
  simp only [Finset.card_univ,Fintype.card_sigma,Fintype.card_fin,Fintype.prod_sigma,
    Finset.prod_const] at h
  rw [count_reaction_density_slots,← mul_sub,abs_mul,abs_of_nonneg hc]
  convert mul_le_mul_of_nonneg_left h hc using 1
  ring

end CompositionalMemory

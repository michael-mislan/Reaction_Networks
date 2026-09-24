import proofs.HeritableCompositions.PartitionTail
import proofs.HeritableCompositions.PartitionDaughters
import proofs.CompositionalMemory.CoupledCounts

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

abbrev WordDraw (k : ℕ) := Fin k × Fin 4 → ℕ

noncomputable def wordDraws {k : ℕ} (n : Fin k → Counts) : Finset (WordDraw k) :=
  Fintype.piFinset (fun i => Finset.range (n i.1 i.2+1))

noncomputable def wordDrawWeight {k : ℕ} (n : Fin k → Counts) (d : WordDraw k) : ℝ :=
  ∏ i, fairBinomialWeight (n i.1 i.2) (d i)

def drawModule {k : ℕ} (d : WordDraw k) (i : Fin k) : Counts := fun a => d (i,a)

theorem word_draw_weight_nonneg {k : ℕ} (n : Fin k → Counts) (d : WordDraw k) :
    0 ≤ wordDrawWeight n d :=
  Finset.prod_nonneg (fun i _ => fairBinomialWeight_nonneg (n i.1 i.2) (d i))

theorem word_draw_weight_sum {k : ℕ} (n : Fin k → Counts) :
    ∑ d ∈ wordDraws n, wordDrawWeight n d = 1 :=
  product_weight_sum (fun i : Fin k × Fin 4 => Finset.range (n i.1 i.2+1))
    (fun i a => fairBinomialWeight (n i.1 i.2) a) (fun i => fair_binomial_sum (n i.1 i.2))

theorem word_draw_marginal {k : ℕ} (n : Fin k → Counts) (i : Fin k × Fin 4) (g : ℕ → ℝ) :
    ∑ d ∈ wordDraws n, wordDrawWeight n d*g (d i) =
      ∑ a ∈ Finset.range (n i.1 i.2+1), fairBinomialWeight (n i.1 i.2) a*g a :=
  product_weight_marginal (fun j : Fin k × Fin 4 => Finset.range (n j.1 j.2+1))
    (fun j a => fairBinomialWeight (n j.1 j.2) a) (fun j => fair_binomial_sum (n j.1 j.2)) i g

theorem draw_module_valid {k : ℕ} (n : Fin k → Counts) (d : WordDraw k)
    (hd : d ∈ wordDraws n) (i : Fin k) : drawModule d i ∈ daughterDraws (n i) := by
  apply Fintype.mem_piFinset.mpr
  intro a
  exact (Fintype.mem_piFinset.mp hd) (i,a)

/-- The same draw determines both daughters; only distinct molecule allocations
are independent. There is no sibling-independence assumption. -/
theorem word_draw_joint_tail {k : ℕ} (n : Fin k → Counts) (N : ℕ) (hN : 0 < N)
    (hn : ∀ i a, (n i a : ℝ) ≤ 70*(N : ℝ)) (δ : ℝ) (hδ : 0 < δ) :
    (∑ d ∈ wordDraws n, wordDrawWeight n d*
      (if ∃ i : Fin k × Fin 4, (N : ℝ)*δ ≤ |(d i : ℝ)-(n i.1 i.2 : ℝ)/2| then 1 else 0)) ≤
      8*(k : ℝ)*Real.exp (-(N : ℝ)*δ^2/35) := by
  classical
  have h := weighted_union_bound (wordDraws n) (wordDrawWeight n)
    (fun d _ => word_draw_weight_nonneg n d)
    (fun i d => (N : ℝ)*δ ≤ |(d i : ℝ)-(n i.1 i.2 : ℝ)/2|)
  have hm (i : Fin k × Fin 4) :
      (∑ d ∈ wordDraws n, wordDrawWeight n d*
        (if (N : ℝ)*δ ≤ |(d i : ℝ)-(n i.1 i.2 : ℝ)/2| then 1 else 0)) ≤
          2*Real.exp (-(N : ℝ)*δ^2/35) := by
    rw [word_draw_marginal n i (fun a => if (N : ℝ)*δ ≤ |(a : ℝ)-(n i.1 i.2 : ℝ)/2| then 1 else 0)]
    simpa only [mul_ite,mul_one,mul_zero] using binomial_volume_tail (n i.1 i.2) N hN (hn i.1 i.2) δ hδ
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hm i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hs
  apply h.trans
  nlinarith only [hs]

end CompositionalMemory

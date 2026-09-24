import proofs.RAFStructuredEnumeration.SupplierParameter

namespace RAFStructuredEnumeration
open RAF RAF.Frankl

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    omega

theorem positive_le_two_pow_pred (n : ℕ) (hn : 0 < n) : n ≤ 2^(n-1) := by
  have h := succ_le_two_pow (n-1)
  omega

theorem product_excess_bound {A : Type*} [Fintype A] (v : A → ℕ)
    (hv : ∀ a, 0 < v a) : (∏ a, v a) ≤ 2^(∑ a, (v a - 1)) := by
  calc
    (∏ a, v a) ≤ ∏ a, 2^(v a - 1) :=
      Finset.prod_le_prod (fun a _ => Nat.zero_le (v a))
        (fun a _ => positive_le_two_pow_pred (v a) (hv a))
    _ = _ := Finset.prod_pow_eq_pow_sum Finset.univ (fun a => v a - 1) 2

variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

theorem resolutions_excess_bound (Q : CRS M R) (cats : R → Finset M) (K : Finset R)
    (hK : ∀ r ∈ K, Supported Q (fun x r => x ∈ cats r) K r) :
    (resolutions Q cats K).card ≤ 2^(supplierExcess Q cats K) := by
  rw [resolutions_card, supplierExcess, pow_add]
  exact Nat.mul_le_mul
    (product_excess_bound _ (fun x => Finset.card_pos.mpr (producerOptions_nonempty Q K x)))
    (product_excess_bound _ (fun r => Finset.card_pos.mpr (catalystOptions_nonempty Q cats K hK r)))

end RAFStructuredEnumeration

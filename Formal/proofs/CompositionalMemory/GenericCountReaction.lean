import proofs.CompositionalMemory.GenericCountDomain

namespace CompositionalMemory

def countReactionNext {d : ℕ} (consume produce n : Fin d → ℕ) : Fin d → ℕ :=
  fun j => n j-consume j+produce j

noncomputable def countReactionDensity {d : ℕ} (c v : ℝ) (consume n : Fin d → ℕ) : ℝ :=
  c*(∏ j, ((n j).descFactorial (consume j):ℝ))/v^(∑ j, consume j)

theorem count_reaction_density_nonneg {d : ℕ} (c v : ℝ) (consume n : Fin d → ℕ)
    (hc : 0 ≤ c) (hv : 0 ≤ v) : 0 ≤ countReactionDensity c v consume n := by
  unfold countReactionDensity
  positivity

theorem count_reaction_density_disabled {d : ℕ} (c v : ℝ) (consume n : Fin d → ℕ)
    (i : Fin d) (hi : n i < consume i) : countReactionDensity c v consume n=0 := by
  have hz : (∏ j, ((n j).descFactorial (consume j):ℝ))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.mpr hi
  simp only [countReactionDensity,hz,mul_zero,zero_div]

theorem count_reaction_density_enabled {d : ℕ} (c v : ℝ) (consume n : Fin d → ℕ)
    (hne : countReactionDensity c v consume n ≠ 0) : ∀ j, consume j ≤ n j := by
  intro j
  by_contra h
  exact hne (count_reaction_density_disabled c v consume n j (by omega))

theorem count_reaction_concentration {d : ℕ} (consume produce n : Fin d → ℕ)
    (v : ℝ) (henabled : ∀ j, consume j ≤ n j) :
    (fun j => (countReactionNext consume produce n j:ℝ)/v) =
      (fun j => (n j:ℝ)/v+((produce j:ℝ)-(consume j:ℝ))/v) := by
  funext j
  simp only [countReactionNext,Nat.cast_add,Nat.cast_sub (henabled j)]
  ring

/-- Rate-weighted binding also holds for disabled reactions: their natural
count update is irrelevant because the exact propensity vanishes. -/
theorem count_reaction_observable_binding {d : ℕ} (consume produce n : Fin d → ℕ)
    (c v : ℝ) (W : (Fin d → ℝ) → ℝ) :
    (v*countReactionDensity c v consume n)*
      (W (fun j => (countReactionNext consume produce n j:ℝ)/v)-W (fun j => (n j:ℝ)/v)) =
    (v*countReactionDensity c v consume n)*
      (W (fun j => (n j:ℝ)/v+((produce j:ℝ)-(consume j:ℝ))/v)-W (fun j => (n j:ℝ)/v)) := by
  by_cases h : countReactionDensity c v consume n=0
  · simp only [h,mul_zero,zero_mul]
  · rw [count_reaction_concentration consume produce n v (count_reaction_density_enabled c v consume n h)]

end CompositionalMemory

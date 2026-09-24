import proofs.CompositionalMemory.TwoSpeciesCoupling

namespace CompositionalMemory

def twoFixedEdgeWeight {k : ℕ} (ε : ℝ) (i j : Fin k) : ℝ := if i=j then 0 else ε

theorem two_fixed_edge_row {k : ℕ} (ε : ℝ) (i : Fin k) :
    (∑ j, twoFixedEdgeWeight ε i j)=((k:ℝ)-1)*ε := by
  classical
  calc
    _ = ∑ j : Fin k, (ε-(if i=j then ε else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i=j <;> simp [twoFixedEdgeWeight,h]
    _ = (k:ℝ)*ε-ε := by rw [Finset.sum_sub_distrib]; simp
    _ = _ := by ring

/-- Every fixed positive per-edge rate eventually violates the rare-high
stationarity condition on dense graphs, even if that rate is very small. -/
theorem two_fixed_edge_obstruction (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (γ : ℝ), 0 ≤ γ →
      ∀ (u : Fin k → TwoPoint) (i : Fin k),
        ‖u i-twoCenter true‖ ≤ 1/10000 →
        (∀ j, j ≠ i → ‖u j-twoCenter false‖ ≤ 1/10000) →
        twoCoupledXDrift γ (twoFixedEdgeWeight ε) u i ≠ 0 := by
  obtain ⟨K,hK⟩ := exists_nat_gt (1+1/(100*ε))
  refine ⟨K,?_⟩
  intro k hk γ hγ u i hhigh hlow
  have hkr : (K:ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < 100*ε := by positivity
  have hbudget : 1 ≤ ((k:ℝ)-1)*(100*ε) :=
    (div_le_iff₀ hden).mp (by linarith only [hK,hkr])
  apply two_rare_high_not_stationary γ hγ (twoFixedEdgeWeight ε)
    (fun i j => by unfold twoFixedEdgeWeight; split <;> positivity)
    (fun i => by simp [twoFixedEdgeWeight]) u i hhigh hlow
  rw [two_fixed_edge_row]
  nlinarith only [hbudget]

end CompositionalMemory

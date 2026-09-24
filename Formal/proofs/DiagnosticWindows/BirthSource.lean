import proofs.DiagnosticWindows.Spectral

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

/-- Six-state uniformized aggregate source. The last state is a positive latch. -/
noncomputable def birthKernel (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1) :
    FiniteKernel (Fin 6) where
  prob x y := if x.val = 5 then (if y.val = 5 then 1 else 0)
    else if y.val = x.val then 1-r x else if y.val = x.val+1 then r x else 0
  nonneg := by
    intro x y
    split_ifs <;> first | positivity | exact (hr x).1 | linarith [(hr x).2]
  row_sum := by
    intro x
    fin_cases x <;> simp only [Fin.sum_univ_succ] <;> norm_num

def uncalled (x : Fin 6) : ℝ := if x.val=5 then 0 else 1

theorem uncalled_indicator : uncalled = FiniteKernel.eventIndicator {x : Fin 6 | x ≠ 5} := by
  funext x
  fin_cases x <;> norm_num [uncalled,FiniteKernel.eventIndicator,Fin.ext_iff]

theorem birth_aggregates (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (x y : Fin 6) (h : (birthKernel r hr).prob x y ≠ 0) :
    x.val ≤ y.val ∧ (y=x ∨ y.val=x.val+1) := by
  by_cases hx : x.val=5
  · have hy : y.val=5 := by
      by_contra hy
      simp [birthKernel,hx,hy] at h
    have he : y=x := Fin.ext (hy.trans hx.symm)
    subst y
    exact ⟨le_rfl,Or.inl rfl⟩
  · by_cases hy : y.val=x.val
    · have he : y=x := Fin.ext hy
      subst y; exact ⟨le_rfl,Or.inl rfl⟩
    · have hn : y.val=x.val+1 := by
        by_contra hn
        simp [birthKernel,hx,hy,hn] at h
      constructor
      · omega
      · exact Or.inr hn

end DiagnosticWindows

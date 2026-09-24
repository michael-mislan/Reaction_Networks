import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace ThermoCoreCompatibility.GeneralCompatibility

/-- A trace consuming fixed coordinate/value tokens cannot consume one twice.
The hypotheses are the local update invariant, not assumed termination. -/
theorem consumed_tokens_injective {V R : Type*} {m : ℕ}
    (coord : R → V) (value : R → ℝ) (A : ℕ → V → ℝ)
    (token : Fin m → R) (hmono : Monotone A)
    (hland : ∀ i, value (token i) ≤ A (i.val + 1) (coord (token i)))
    (hstrict : ∀ i, A i.val (coord (token i)) < value (token i)) :
    Function.Injective token := by
  have hne : ∀ i j : Fin m, i < j → token i ≠ token j := by
    intro i j hij heq
    have hstep : i.val + 1 ≤ j.val := hij
    have hab := hmono hstep (coord (token i))
    have hl := hland i
    have hs := hstrict j
    rw [heq] at hab hl
    linarith
  intro i j heq
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (hne i j hij heq)
  · exact hij
  · exact False.elim (hne j i hij heq.symm)

theorem cycle_jump_count_bound {V R : Type*} [Fintype R] {m : ℕ}
    (coord : R → V) (value : R → ℝ) (A : ℕ → V → ℝ)
    (token : Fin m → R) (hmono : Monotone A)
    (hland : ∀ i, value (token i) ≤ A (i.val + 1) (coord (token i)))
    (hstrict : ∀ i, A i.val (coord (token i)) < value (token i)) :
    m ≤ Fintype.card R := by
  simpa using Fintype.card_le_of_injective token
    (consumed_tokens_injective coord value A token hmono hland hstrict)

/-- The actual single-anchor update semantics forbid an infinite successful run. -/
theorem no_infinite_anchor_updates {V R : Type*} [Fintype R] [DecidableEq V]
    (coord : R → V) (value : R → ℝ) (A : ℕ → V → ℝ) (token : ℕ → R)
    (hupdate : ∀ n, A (n+1) = Function.update (A n) (coord (token n)) (value (token n)))
    (hstrict : ∀ n, A n (coord (token n)) < value (token n)) : False := by
  have hmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro n v
    rw [hupdate n]
    by_cases hv : v = coord (token n)
    · subst v
      simpa using (hstrict n).le
    · simp [Function.update_of_ne hv]
  have hland (n : ℕ) : value (token n) ≤ A (n+1) (coord (token n)) := by
    rw [hupdate n]
    simp
  have hbound := cycle_jump_count_bound (m := Fintype.card R + 1) coord value A
    (fun i => token i.val) hmono (fun i => hland i.val) (fun i => hstrict i.val)
  exact Nat.not_succ_le_self _ hbound

end ThermoCoreCompatibility.GeneralCompatibility

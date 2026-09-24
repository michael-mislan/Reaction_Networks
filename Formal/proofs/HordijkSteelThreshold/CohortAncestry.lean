import Mathlib.Tactic

namespace HordijkSteelThreshold

/-- Rooted catalyst ancestry specifies the cohort number: roots are startup
components and a child's witness belongs to the immediately preceding cohort. -/
def IsCohortRank {V : Type*} (root : V → Prop) (parent : V → V)
    (rank : V → ℕ) : Prop :=
  (∀ x, root x ↔ rank x = 0) ∧
  (∀ x, ¬ root x → rank x = rank (parent x) + 1)

/-- A fixed catalyst-ancestry forest has at most one chronological labeling.
This removes an additional time-label multiplicity; source extraction and the
number of forests themselves require separate proofs. -/
theorem cohortRank_unique {V : Type*} {root : V → Prop} {parent : V → V}
    {rank other : V → ℕ} (hr : IsCohortRank root parent rank)
    (ho : IsCohortRank root parent other) : rank = other := by
  have aux : ∀ k x, rank x = k → other x = k := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact (ho.1 x).mp ((hr.1 x).mpr hx)
    | succ k ih =>
      intro x hx
      have hn : ¬ root x := by
        intro h
        have hz := (hr.1 x).mp h
        omega
      have hp : rank (parent x) = k := by
        have hs := hr.2 x hn
        omega
      rw [ho.2 x hn, ih (parent x) hp]
  funext x
  exact (aux (rank x) x rfl).symm

end HordijkSteelThreshold

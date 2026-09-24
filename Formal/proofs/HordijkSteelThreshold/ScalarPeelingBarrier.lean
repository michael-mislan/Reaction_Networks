import Mathlib.Tactic

namespace HordijkSteelThreshold

def scalarActive {R : Type*} (reactions : Finset R) (threshold : R → ℕ)
    (k : ℕ) : Finset R := reactions.filter (fun r => threshold r ≤ k)

theorem scalarActive_mono {R : Type*} (reactions : Finset R) (threshold : R → ℕ)
    {a b : ℕ} (h : a ≤ b) :
    scalarActive reactions threshold a ⊆ scalarActive reactions threshold b := by
  intro r hr
  obtain ⟨hrR, hrk⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨hrR, hrk.trans h⟩

def scalarPoolAt {X R : Type*} [Fintype X]
    (reactions : Finset R) (threshold : R → ℕ) (closure : Finset R → Finset X) :
    ℕ → Finset X
  | 0 => Finset.univ
  | t + 1 => closure (scalarActive reactions threshold
      (scalarPoolAt reactions threshold closure t).card)

/-- A static closure with mass at least its threshold is contained in every
scalar-feedback iterate. No random-pool independence is used here. -/
theorem scalarPoolAt_contains_barrier {X R : Type*} [Fintype X]
    (reactions : Finset R) (threshold : R → ℕ) (closure : Finset R → Finset X)
    (hmono : Monotone closure) (k : ℕ)
    (hk : k ≤ (closure (scalarActive reactions threshold k)).card) (t : ℕ) :
    closure (scalarActive reactions threshold k) ⊆
      scalarPoolAt reactions threshold closure t := by
  induction t with
  | zero => exact Finset.subset_univ _
  | succ t ih =>
    have hmass : k ≤ (scalarPoolAt reactions threshold closure t).card :=
      hk.trans (Finset.card_le_card ih)
    exact hmono (scalarActive_mono reactions threshold hmass)

theorem scalarPoolAt_card_ge_barrier {X R : Type*} [Fintype X]
    (reactions : Finset R) (threshold : R → ℕ) (closure : Finset R → Finset X)
    (hmono : Monotone closure) (k : ℕ)
    (hk : k ≤ (closure (scalarActive reactions threshold k)).card) (t : ℕ) :
    k ≤ (scalarPoolAt reactions threshold closure t).card :=
  hk.trans (Finset.card_le_card
    (scalarPoolAt_contains_barrier reactions threshold closure hmono k hk t))

end HordijkSteelThreshold

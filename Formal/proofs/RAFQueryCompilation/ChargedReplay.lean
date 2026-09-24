import proofs.RAFQueryCompilation.LocalWorkspace

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Declared comparison/copy budget for linear finite-set primitives.
Equality of individual identifiers is one primitive here; bit costs are separate.
This is a charge semantics, not a theorem about the Lean runtime allocator. -/
def replayStepCharge (Q : CRS M R) (S : Finset R) (pool : Finset M) (r : R) : ℕ :=
  1 + S.card + if r ∈ S then
    ((Q.inputs r).card + 1) * (pool.card + 1) +
      if Q.inputs r ⊆ pool then (pool.card + (Q.outputs r).card + 1)^2 else 0
  else 0

def chargedReplayFrom (Q : CRS M R) (S : Finset R) :
    List R → Finset M → Finset M × ℕ
  | [], pool => (pool, 0)
  | r :: rs, pool =>
    let tail := chargedReplayFrom Q S rs (scheduleStep Q S pool r)
    (tail.1, replayStepCharge Q S pool r + tail.2)

theorem chargedReplay_refines (Q : CRS M R) (S : Finset R) (order : List R)
    (pool : Finset M) :
    (chargedReplayFrom Q S order pool).1 = order.foldl (scheduleStep Q S) pool := by
  induction order generalizing pool with
  | nil => rfl
  | cons r rs ih => exact ih _

theorem replayStepCharge_le (Q : CRS M R) (S : Finset R) (pool : Finset M)
    (r : R) (e i o p : ℕ) (he : S.card ≤ e) (hp : pool.card ≤ p)
    (hi : ∀ s ∈ S, (Q.inputs s).card ≤ i)
    (ho : ∀ s ∈ S, (Q.outputs s).card ≤ o) :
    replayStepCharge Q S pool r ≤ 1+e+(i+1)*(p+1)+(p+o+1)^2 := by
  by_cases hr : r ∈ S
  · have hi' := Nat.mul_le_mul (Nat.add_le_add_right (hi r hr) 1)
        (Nat.add_le_add_right hp 1)
    have ho' : (pool.card + (Q.outputs r).card + 1)^2 ≤ (p+o+1)^2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hp (ho r hr)) 1) 2
    by_cases hf : Q.inputs r ⊆ pool
    · simp only [replayStepCharge, if_pos hr, if_pos hf]
      omega
    · simp only [replayStepCharge, if_pos hr, if_neg hf]
      omega
  · simp only [replayStepCharge, if_neg hr]
    omega

/-- The charge bound uses a source envelope and per-row source arities, never
the ambient molecule or reaction universe. Disabled out-of-region entries do
not require incidence-row bounds. -/
theorem chargedReplay_bound (Q : CRS M R) (S H : Finset M)
    (A : Finset R) (e i o : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) (hS : S ⊆ H) (order : List R) :
    (chargedReplayFrom Q A order S).2 ≤
      order.length * (1+e+(i+1)*(H.card+1)+(H.card+o+1)^2) := by
  induction order generalizing S with
  | nil => simp [chargedReplayFrom]
  | cons r rs ih =>
    have hp : scheduleStep Q A S r ⊆ H := by
      unfold scheduleStep
      split
      next h => exact Finset.union_subset hS (hout r h.1)
      next => exact hS
    have ht := ih _ hp
    have hc := replayStepCharge_le Q A S r e i o H.card he
      (Finset.card_le_card hS) hi ho
    simp only [chargedReplayFrom, List.length_cons]
    nlinarith

end RAFQueryCompilation

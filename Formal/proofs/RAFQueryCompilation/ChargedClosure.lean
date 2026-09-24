import proofs.RAFQueryCompilation.ChargedReplay

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- A declared linear-set comparison/copy budget for closure construction and
terminal equality. It includes all active input tests and possible output unions. -/
def closureTerminalCharge (Q : CRS M R) (A : Finset R) (pool : Finset M) : ℕ :=
  1 + (∑ r ∈ A, ((Q.inputs r).card+1)*(pool.card+1)) +
    2 * (pool.card + (∑ r ∈ A, (Q.outputs r).card) + 1)^2

def chargedClosure (Q : CRS M R) (A : Finset R) (order : List R) :
    Option (Finset M) × ℕ :=
  let replay := chargedReplayFrom Q A order Q.food
  (if closureStep Q A replay.1 = replay.1 then some replay.1 else none,
    Q.food.card + replay.2 + closureTerminalCharge Q A replay.1)

theorem chargedClosure_refines (Q : CRS M R) (A : Finset R) (order : List R) :
    (chargedClosure Q A order).1 = checkClosure Q A order := by
  simp only [chargedClosure, chargedReplay_refines, checkClosure, replaySchedule]

omit [DecidableEq R] in
theorem closureTerminalCharge_le (Q : CRS M R) (A : Finset R) (pool : Finset M)
    (e i o p : ℕ) (he : A.card ≤ e) (hp : pool.card ≤ p)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o) :
    closureTerminalCharge Q A pool ≤
      1+e*((i+1)*(p+1))+2*(p+e*o+1)^2 := by
  have hin : (∑ r ∈ A, ((Q.inputs r).card+1)*(pool.card+1)) ≤ e*((i+1)*(p+1)) := by
    calc
      _ ≤ ∑ _r ∈ A, (i+1)*(p+1) := Finset.sum_le_sum fun r hr =>
        Nat.mul_le_mul (Nat.add_le_add_right (hi r hr) 1) (Nat.add_le_add_right hp 1)
      _ = A.card*((i+1)*(p+1)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ he
  have hout : (∑ r ∈ A, (Q.outputs r).card) ≤ e*o := by
    calc
      _ ≤ ∑ _r ∈ A, o := Finset.sum_le_sum ho
      _ = A.card*o := by simp
      _ ≤ _ := Nat.mul_le_mul_right o he
  have hs := Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hp hout) 1) 2
  unfold closureTerminalCharge
  omega

theorem checkedClosure_pool_subset (Q : CRS M R) (A : Finset R) (H : Finset M)
    (hf : Q.food ⊆ H) (hout : ∀ r ∈ A, Q.outputs r ⊆ H)
    (order : List R) {pool : Finset M} (h : checkClosure Q A order = some pool) :
    pool ⊆ H := by
  have hp : replaySchedule Q A order = pool := by
    dsimp only [checkClosure] at h
    split at h
    · exact Option.some.inj h
    · contradiction
  rw [← hp]
  apply (replaySchedule_subset_envelope Q A A (Finset.Subset.refl _) order).trans
  apply Finset.union_subset hf
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨r,hr,hx⟩
  exact hout r hr hx

theorem chargedClosure_bound (Q : CRS M R) (A : Finset R) (H : Finset M)
    (e i o : ℕ) (he : A.card ≤ e)
    (hi : ∀ r ∈ A, (Q.inputs r).card ≤ i)
    (ho : ∀ r ∈ A, (Q.outputs r).card ≤ o)
    (hout : ∀ r ∈ A, Q.outputs r ⊆ H) (hf : Q.food ⊆ H) (order : List R) :
    (chargedClosure Q A order).2 ≤ H.card +
      order.length*(1+e+(i+1)*(H.card+1)+(H.card+o+1)^2) +
      (1+e*((i+1)*(H.card+1))+2*(H.card+e*o+1)^2) := by
  have hpool : (chargedReplayFrom Q A order Q.food).1 ⊆ H := by
    rw [chargedReplay_refines]
    change replaySchedule Q A order ⊆ H
    apply (replaySchedule_subset_envelope Q A A (Finset.Subset.refl _) order).trans
    apply Finset.union_subset hf
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨r,hr,hx⟩
    exact hout r hr hx
  have hr := chargedReplay_bound Q Q.food H A e i o he hi ho hout hf order
  have hc := closureTerminalCharge_le Q A _ e i o H.card he
    (Finset.card_le_card hpool) hi ho
  have hfood := Finset.card_le_card hf
  simp only [chargedClosure]
  omega

end RAFQueryCompilation

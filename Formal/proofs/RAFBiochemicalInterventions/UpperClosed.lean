import proofs.RAFBiochemicalInterventions.RankedClosed

namespace RAFBiochemicalLiteral

def upperCheck (rows : List Row) (food : List Nat) (prior : Row → Bool)
    (pool : Nat → Bool) (next : Row → Bool) : Bool :=
  decide ((∀ x ∈ food, pool x = true) ∧ ∀ r ∈ rows, prior r = true →
    ((∀ x ∈ r.inputs, pool x = true) → ∀ y ∈ r.outputs, pool y = true) ∧
    ((∀ x ∈ r.inputs, pool x = true) → r.catalyst.test pool = true → next r = true))

theorem upper_generated (rows : List Row) (food : List Nat) (prior : Row → Bool)
    (pool : Nat → Bool) (next : Row → Bool) (h : upperCheck rows food prior pool next = true)
    (S : List Row) (hS : Subrows S (selected rows prior)) :
    ∀ x, Generated S food x → pool x = true := by
  have hh := of_decide_eq_true h
  change (∀ x ∈ food, pool x = true) ∧ (∀ r ∈ rows, prior r = true →
    ((∀ x ∈ r.inputs, pool x = true) → ∀ y ∈ r.outputs, pool y = true) ∧
    ((∀ x ∈ r.inputs, pool x = true) → r.catalyst.test pool = true → next r = true)) at hh
  intro x hx
  induction hx with
  | food hx => exact hh.1 _ hx
  | reaction r hr _ y hy ih =>
    have hr' := List.mem_filter.mp (hS r hr)
    exact (hh.2 r hr'.1 hr'.2).1 ih y hy

theorem upper_raf (rows : List Row) (food : List Nat) (prior : Row → Bool)
    (pool : Nat → Bool) (next : Row → Bool) (h : upperCheck rows food prior pool next = true)
    (S : List Row) (hS : Subrows S (selected rows prior)) (hraf : RAF S food) :
    Subrows S (selected rows next) := by
  have hh := of_decide_eq_true h
  change (∀ x ∈ food, pool x = true) ∧ (∀ r ∈ rows, prior r = true →
    ((∀ x ∈ r.inputs, pool x = true) → ∀ y ∈ r.outputs, pool y = true) ∧
    ((∀ x ∈ r.inputs, pool x = true) → r.catalyst.test pool = true → next r = true)) at hh
  have hp := upper_generated rows food prior pool next h S hS
  intro r hr
  have hr' := List.mem_filter.mp (hS r hr)
  have hs := hraf.2 r hr
  exact List.mem_filter.mpr ⟨hr'.1,(hh.2 r hr'.1 hr'.2).2
    (fun x hx => hp x (hs.1 x hx))
    ((r.catalyst.test_iff pool).mpr (r.catalyst.sat_mono hp hs.2))⟩

def closeCheck (rows : List Row) (pool : Nat → Bool) (keep : Row → Bool) : Bool :=
  decide (∀ r ∈ rows, (∀ x ∈ r.inputs, pool x = true) →
    r.catalyst.test pool = true → keep r = true)

theorem upper_append (A B : List Row) (food : List Nat) (prior : Row → Bool)
    (pool : Nat → Bool) (next : Row → Bool)
    (ha : upperCheck A food prior pool next = true)
    (hb : upperCheck B food prior pool next = true) :
    upperCheck (A ++ B) food prior pool next = true := by
  unfold upperCheck at *
  have hA := of_decide_eq_true ha
  have hB := of_decide_eq_true hb
  apply decide_eq_true
  refine ⟨hA.1,?_⟩
  intro r hr
  exact (List.mem_append.mp hr).elim (hA.2 r) (hB.2 r)

theorem close_append (A B : List Row) (pool : Nat → Bool) (keep : Row → Bool)
    (ha : closeCheck A pool keep = true) (hb : closeCheck B pool keep = true) :
    closeCheck (A ++ B) pool keep = true := by
  unfold closeCheck at *
  have hA := of_decide_eq_true ha
  have hB := of_decide_eq_true hb
  apply decide_eq_true
  intro r hr
  exact (List.mem_append.mp hr).elim (hA r) (hB r)

theorem closed_of_upper (rows : List Row) (food : List Nat) (keep : Row → Bool)
    (pool : Nat → Bool) (hm : RAF (selected rows keep) food)
    (hp : ∀ x, Generated (selected rows keep) food x → pool x = true)
    (h : closeCheck rows pool keep = true) : ClosedRAF rows (selected rows keep) food := by
  have hh : ∀ r ∈ rows, (∀ x ∈ r.inputs, pool x = true) →
    r.catalyst.test pool = true → keep r = true := of_decide_eq_true h
  refine ⟨hm,?_⟩
  intro r hr hi hc
  exact List.mem_filter.mpr ⟨hr,hh r hr (fun x hx => hp x (hi x hx))
    ((r.catalyst.test_iff pool).mpr (r.catalyst.sat_mono hp hc))⟩

end RAFBiochemicalLiteral

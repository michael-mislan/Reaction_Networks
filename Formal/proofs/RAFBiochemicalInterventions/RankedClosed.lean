import proofs.RAFBiochemicalInterventions.LiteralStructure

namespace RAFBiochemicalLiteral

def Formula.test (p : Nat → Bool) : Formula → Bool
  | .atom x => p x
  | .both a b => a.test p && b.test p
  | .either a b => a.test p || b.test p
  | .yes => true

theorem Formula.test_iff (f : Formula) (p : Nat → Bool) :
    f.test p = true ↔ f.Sat (fun x => p x = true) := by
  induction f with
  | atom x => rfl
  | both a b ha hb => simp [test, Sat, ha, hb]
  | either a b ha hb => simp [test, Sat, ha, hb]
  | yes => simp [test, Sat]

inductive RowTree where
  | nil
  | node (left : RowTree) (row : Row) (right : RowTree)

def RowTree.values : RowTree → List Row
  | .nil => []
  | .node l r u => l.values ++ r :: u.values

def RowTree.get : RowTree → Nat → Option Row
  | .nil, _ => none
  | .node l r u, i => if i = r.direction then some r else
      if i < r.direction then l.get i else u.get i

theorem RowTree.get_mem (t : RowTree) (i : Nat) (r : Row) (h : t.get i = some r) :
    r ∈ t.values := by
  induction t with
  | nil => simp [get] at h
  | node l s u hl hu =>
    simp only [get] at h
    split at h
    next =>
      have he : s = r := Option.some.inj h
      subst s
      simp [values]
    next =>
      split at h
      next => exact List.mem_append_left _ (hl h)
      next => exact List.mem_append_right _ (List.mem_cons_of_mem _ (hu h))

def selected (rows : List Row) (keep : Row → Bool) : List Row := rows.filter keep
def known (n : Nat) (rank : Nat → Nat) (x : Nat) : Bool := decide (x < n ∧ 0 < rank x)
def earlier (n : Nat) (rank : Nat → Nat) (x y : Nat) : Bool :=
  known n rank y && decide (rank y < rank x)

def moleculeCheck (t : RowTree) (food : List Nat) (keep : Row → Bool)
    (n : Nat) (rank owner : Nat → Nat) (x : Nat) : Bool :=
  if known n rank x then
    if food.contains x then true else
      match t.get (owner x) with
      | none => false
      | some r => keep r && r.outputs.contains x &&
          r.inputs.all (earlier n rank x) && r.catalyst.test (earlier n rank x)
  else true

def rankCheck (t : RowTree) (food : List Nat) (keep : Row → Bool)
    (n : Nat) (rank owner : Nat → Nat) : Bool :=
  (List.range n).all (moleculeCheck t food keep n rank owner) &&
  (t.values.all fun r => !keep r ||
    (r.inputs.all (known n rank) && r.catalyst.test (known n rank)))

theorem ranked_available (rows : List Row) (food : List Nat) (keep : Row → Bool)
    (t : RowTree) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
    (h : rankCheck t food keep n rank owner = true)
    (P : Nat → Prop) (hf : ∀ x ∈ food, P x)
    (hs : ∀ r ∈ rows, keep r = true → (∀ x ∈ r.inputs, P x) → r.catalyst.Sat P →
      ∀ y ∈ r.outputs, P y) : ∀ x, known n rank x = true → P x := by
  intro x
  have hall : ∀ k, ∀ x, rank x = k → known n rank x = true → P x := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx hk
      have hxn : x ∈ List.range n := by simpa [known] using (show x < n from (of_decide_eq_true hk).1)
      have hm : moleculeCheck t food keep n rank owner x = true :=
        List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 x hxn
      simp only [moleculeCheck, hk, ↓reduceIte] at hm
      split at hm
      next hf' => exact hf x (by simpa using hf')
      next =>
        split at hm
        next => contradiction
        next r he =>
          have hb := Bool.and_eq_true_iff.mp hm
          have ha := Bool.and_eq_true_iff.mp hb.1
          have hc := Bool.and_eq_true_iff.mp ha.1
          have hprev : ∀ y, earlier n rank x y = true → P y := by
            intro y hy
            have hh := Bool.and_eq_true_iff.mp hy
            exact ih (rank y) (by simpa [hx] using of_decide_eq_true hh.2) y rfl hh.1
          exact hs r (ht ▸ t.get_mem (owner x) r he) hc.1
            (fun y hy => hprev y (List.all_eq_true.mp ha.2 y hy))
            (r.catalyst.sat_mono hprev ((r.catalyst.test_iff _).mp hb.2)) x
            (by simpa using hc.2)
  exact hall (rank x) x rfl

theorem rank_forces (rows : List Row) (food : List Nat) (keep : Row → Bool)
    (t : RowTree) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
    (h : rankCheck t food keep n rank owner = true)
    (C : List Row) (hc : ClosedRAF rows C food) : Subrows (selected rows keep) C := by
  have hp := ranked_available rows food keep t ht n rank owner h (Generated C food)
    (fun _ hx => Generated.food hx)
    (fun r hr _ hi hcat y hy => Generated.reaction r (hc.2 r hr hi hcat) hi y hy)
  intro r hr
  have hh := List.mem_filter.mp hr
  have htmem : r ∈ t.values := ht.symm ▸ hh.1
  have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 r htmem
  simp only [hh.2, Bool.not_true, Bool.false_or] at hs
  have hv := Bool.and_eq_true_iff.mp hs
  exact hc.2 r hh.1 (fun x hx => hp x (List.all_eq_true.mp hv.1 x hx))
    (r.catalyst.sat_mono hp ((r.catalyst.test_iff _).mp hv.2))

theorem rank_raf (rows : List Row) (food : List Nat) (keep : Row → Bool)
    (t : RowTree) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
    (h : rankCheck t food keep n rank owner = true)
    (hne : selected rows keep ≠ []) : RAF (selected rows keep) food := by
  have hp := ranked_available rows food keep t ht n rank owner h
    (Generated (selected rows keep) food) (fun _ hx => Generated.food hx)
    (fun r hr hk hi _ y hy => Generated.reaction r (List.mem_filter.mpr ⟨hr,hk⟩) hi y hy)
  refine ⟨hne,?_⟩
  intro r hr
  have hh := List.mem_filter.mp hr
  have hs := List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2 r (ht.symm ▸ hh.1)
  simp only [hh.2, Bool.not_true, Bool.false_or] at hs
  have hv := Bool.and_eq_true_iff.mp hs
  exact ⟨fun x hx => hp x (List.all_eq_true.mp hv.1 x hx),
    r.catalyst.sat_mono hp ((r.catalyst.test_iff _).mp hv.2)⟩

/-- The lower constructive certificate and an RAF upper bound meet extensionally. -/
theorem unique_closed_of_bounds (rows M : List Row) (food : List Nat)
    (hm : RAF M food)
    (hlower : ∀ C, ClosedRAF rows C food → Subrows M C)
    (hupper : ∀ S, Subrows S rows → RAF S food → Subrows S M)
    (hclosed : ClosedRAF rows M food) :
    ∀ C, Subrows C rows → (ClosedRAF rows C food ↔ SameRows C M) := by
  intro C hc
  constructor
  · intro h
    exact ⟨hupper C hc h.1,hlower C h⟩
  · intro he
    refine ⟨raf_of_same_rows ⟨he.2,he.1⟩ hm,?_⟩
    intro r hr hi hcat
    have hgen := fun x (hx : Generated C food x) => generated_mono he.1 hx
    exact he.2 r (hclosed.2 r hr (fun x hx => hgen x (hi x hx))
      (r.catalyst.sat_mono hgen hcat))

end RAFBiochemicalLiteral

import proofs.RAFBiochemicalInterventions.RankedClosed

namespace RAFBiochemicalLiteral.Indexed

structure RowIndex where
  blocks : Array (List Row)

def RowIndex.values (t : RowIndex) : List Row := t.blocks.toList.flatten
def RowIndex.get (t : RowIndex) (i : Nat) : Option Row :=
  t.blocks[i / 128]? >>= fun block => block[i % 128]?
theorem RowIndex.get_mem (t : RowIndex) (i : Nat) (r : Row) (h : t.get i = some r) : r ∈ t.values := by
  unfold get at h
  cases he : t.blocks[i / 128]? with
  | none => simp [he] at h
  | some block =>
    have hr : r ∈ block := List.mem_of_getElem? (by simpa [he] using h)
    have hb : block ∈ t.blocks.toList := by simpa using Array.mem_of_getElem? he
    exact List.mem_flatten.mpr ⟨block,hb,hr⟩

def selected (rows : List Row) (keep : Row → Bool) : List Row := rows.filter keep
def known (n : Nat) (rank : Nat → Nat) (x : Nat) : Bool := decide (x < n ∧ 0 < rank x)
def earlier (n : Nat) (rank : Nat → Nat) (x y : Nat) : Bool :=
  known n rank y && decide (rank y < rank x)

def moleculeCheck (t : RowIndex) (food : List Nat) (keep : Row → Bool)
    (n : Nat) (rank owner : Nat → Nat) (x : Nat) : Bool :=
  if known n rank x then
    if food.contains x then true else
      match t.get (owner x) with
      | none => false
      | some r => keep r && r.outputs.contains x &&
          r.inputs.all (earlier n rank x) && r.catalyst.test (earlier n rank x)
  else true

def rankCheck (t : RowIndex) (food : List Nat) (keep : Row → Bool)
    (n : Nat) (rank owner : Nat → Nat) : Bool :=
  (List.range n).all (moleculeCheck t food keep n rank owner) &&
  (t.values.all fun r => !keep r ||
    (r.inputs.all (known n rank) && r.catalyst.test (known n rank)))

theorem ranked_available (rows : List Row) (food : List Nat) (keep : Row → Bool)
    (t : RowIndex) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
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
    (t : RowIndex) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
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
    (t : RowIndex) (ht : t.values = rows) (n : Nat) (rank owner : Nat → Nat)
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

end RAFBiochemicalLiteral.Indexed

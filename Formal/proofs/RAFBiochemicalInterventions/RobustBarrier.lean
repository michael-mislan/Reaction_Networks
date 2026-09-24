import proofs.RAFBiochemicalInterventions.LiteralStructure

namespace RAFBiochemicalLiteral

def Siphon (rows : List Row) (B : List Nat) : Prop :=
  ∀ r ∈ rows, ∀ x ∈ r.outputs, x ∈ B → ∃ y ∈ r.inputs, y ∈ B

theorem checked_siphon (rows : List Row) (food B D : List Nat)
    (h : checkBarrier rows food B D = true) : Siphon (remaining rows D) B :=
  (show Barrier (remaining rows D) food B from of_decide_eq_true h).2

theorem siphon_food_independent (rows : List Row) (B F : List Nat)
    (hs : Siphon rows B) (hf : ∀ x ∈ F, x ∉ B) :
    ∀ x, Generated rows F x → x ∉ B := fun _ hx => barrier_exclusion ⟨hf,hs⟩ hx

theorem siphon_subrows {rows S : List Row} {B : List Nat}
    (h : Siphon rows B) (hs : Subrows S rows) : Siphon S B :=
  fun r hr => h r (hs r hr)

theorem siphon_append {rows added : List Row} {B : List Nat}
    (h : Siphon rows B) (ha : Siphon added B) : Siphon (rows ++ added) B := by
  intro r hr
  exact (List.mem_append.mp hr).elim (h r) (ha r)

def annotate (c : Nat → Formula) (r : Row) : Row := {r with catalyst := c r.direction}

theorem siphon_annotate (rows : List Row) (B : List Nat) (c : Nat → Formula)
    (h : Siphon rows B) : Siphon (rows.map (annotate c)) B := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact h s hs

theorem generated_enlarge (S : List Row) (F F' : List Nat) (c : Nat → Formula)
    (hf : ∀ x ∈ F, x ∈ F') : ∀ x, Generated S F x → Generated (S.map (annotate c)) F' x := by
  intro x hx
  induction hx with
  | food hx => exact Generated.food (hf _ hx)
  | reaction r hr _ y hy ih =>
    exact Generated.reaction (annotate c r) (List.mem_map.mpr ⟨r,hr,rfl⟩) ih y hy

def Weakens (rows : List Row) (c : Nat → Formula) : Prop :=
  ∀ r ∈ rows, ∀ P : Nat → Prop, r.catalyst.Sat P → (c r.direction).Sat P

theorem capable_enlarge (rows : List Row) (F F' : List Nat) (c : Nat → Formula) (p : Nat)
    (hf : ∀ x ∈ F, x ∈ F') (hw : Weakens rows c) (h : Capable rows F p) :
    Capable (rows.map (annotate c)) F' p := by
  obtain ⟨S,hs,hraf,hp⟩ := h
  refine ⟨S.map (annotate c),?_,⟨?_,?_⟩,generated_enlarge S F F' c hf p hp⟩
  · intro r hr
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hr
    exact List.mem_map.mpr ⟨s,hs s hs',rfl⟩
  · intro he
    exact hraf.1 (List.map_eq_nil_iff.mp he)
  · intro r hr
    obtain ⟨s,hs',rfl⟩ := List.mem_map.mp hr
    have hg := generated_enlarge S F F' c hf
    exact ⟨fun x hx => hg x ((hraf.2 s hs').1 x hx),
      hw s (hs s hs') _ (s.catalyst.sat_mono hg (hraf.2 s hs').2)⟩

theorem remaining_annotate (rows : List Row) (D : List Nat) (c : Nat → Formula) :
    remaining (rows.map (annotate c)) D = (remaining rows D).map (annotate c) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, remaining, List.filter_cons]
    change (if !D.contains r.action then annotate c r :: remaining (rs.map (annotate c)) D
      else remaining (rs.map (annotate c)) D) = _
    split <;> simp_all [remaining,annotate]

theorem robust_minimal (rows : List Row) (F F' B D : List Nat) (c : Nat → Formula) (p : Nat)
    (hb : Siphon (remaining rows D) B) (hp : p ∈ B)
    (hf : ∀ x ∈ F, x ∈ F') (havoid : ∀ x ∈ F', x ∉ B) (hw : Weakens rows c)
    (hr : ∀ a ∈ D, Capable (remaining rows (restore D a)) F p) :
    MinimalCut (rows.map (annotate c)) F' p D := by
  apply minimal_cut_of_restorations
  · apply not_capable_of_not_generated
    rw [remaining_annotate]
    exact fun hx => siphon_food_independent _ B F' (siphon_annotate _ B c hb) havoid p hx hp
  · intro a ha
    rw [remaining_annotate]
    apply capable_enlarge _ F F' c p hf ?_ (hr a ha)
    intro r hr'
    exact hw r (List.mem_filter.mp hr').1

inductive FiringTrace (rows : List Row) : List Nat → List Nat → Prop
  | refl (X) : FiringTrace rows X X
  | step {X Y Z} (h : FiringTrace rows X Y) (r : Row) (hr : r ∈ rows)
      (hi : ∀ x ∈ r.inputs, x ∈ Y)
      (hz : ∀ x ∈ Z, x ∈ Y ∨ x ∈ r.outputs) : FiringTrace rows X Z

theorem firing_invariant (rows : List Row) (B X Y : List Nat)
    (hs : Siphon rows B) (hx : ∀ x ∈ X, x ∉ B) (h : FiringTrace rows X Y) :
    ∀ y ∈ Y, y ∉ B := by
  induction h with
  | refl => exact hx
  | step _ r hr hi hz ih =>
    intro y hy hyb
    rcases hz y hy with hy | hy
    · exact ih y hy hyb
    · obtain ⟨x,hxi,hxb⟩ := hs r hr y hy hyb
      exact ih x (hi x hxi) hxb

end RAFBiochemicalLiteral

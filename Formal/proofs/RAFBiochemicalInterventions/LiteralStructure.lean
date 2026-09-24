import proofs.RAFBiochemicalInterventions.LiteralSupport

namespace RAFBiochemicalLiteral

theorem checked_raf (rows : List Row) (food : List Nat) (S order : List Row) (p : Nat)
    (h : checkSupport rows food S order p = true) : RAF S food := by
  have hh := of_decide_eq_true h
  change (∀ r ∈ S, r ∈ rows) ∧ S ≠ [] ∧
    (∀ r ∈ S, (∀ x ∈ r.inputs, x ∈ replay S food order) ∧
      r.catalyst.Sat (fun x => x ∈ replay S food order)) ∧ p ∈ replay S food order at hh
  have hp := replay_sound S food food order (fun _ hx => Generated.food hx)
  refine ⟨hh.2.1,?_⟩
  intro r hr
  exact ⟨fun x hx => hp x ((hh.2.2.1 r hr).1 x hx),
    r.catalyst.sat_mono hp (hh.2.2.1 r hr).2⟩

def Subrows (S T : List Row) : Prop := ∀ r ∈ S, r ∈ T
def SameRows (S T : List Row) : Prop := Subrows S T ∧ Subrows T S
def Irreducible (S : List Row) (food : List Nat) : Prop :=
  RAF S food ∧ ∀ T, Subrows T S → RAF T food → Subrows S T

def eraseRow (S : List Row) (r : Row) : List Row := S.filter (fun s => s != r)

/-- Test whether the residual contains any RAF, not whether the residual itself is RAF. -/
theorem irreducible_iff_residual_empty (S : List Row) (food : List Nat) :
    Irreducible S food ↔ RAF S food ∧ ∀ r ∈ S,
      ¬ ∃ T, Subrows T (eraseRow S r) ∧ RAF T food := by
  constructor
  · rintro ⟨hs,hmin⟩
    refine ⟨hs,?_⟩
    rintro r hr ⟨T,ht,hraf⟩
    have hsub : Subrows T S := fun s hs => (List.mem_filter.mp (ht s hs)).1
    have hh := ht r (hmin T hsub hraf r hr)
    simp [eraseRow] at hh
  · rintro ⟨hs,hempty⟩
    refine ⟨hs,?_⟩
    intro T ht hraf r hr
    apply Classical.byContradiction
    intro hn
    apply hempty r hr
    refine ⟨T,?_,hraf⟩
    intro s hs
    have hne : s ≠ r := fun he => hn (he ▸ hs)
    simpa [eraseRow] using And.intro (ht s hs) hne

def ClosedRAF (rows S : List Row) (food : List Nat) : Prop :=
  RAF S food ∧ ∀ r ∈ rows, (∀ x ∈ r.inputs, Generated S food x) →
    r.catalyst.Sat (Generated S food) → r ∈ S

def checkClosed (rows S : List Row) (food pool : List Nat) : Bool :=
  decide ((∀ x ∈ food, x ∈ pool) ∧
    (∀ r ∈ S, (∀ x ∈ r.inputs, x ∈ pool) → ∀ y ∈ r.outputs, y ∈ pool) ∧
    ∀ r ∈ rows, (∀ x ∈ r.inputs, x ∈ pool) → r.catalyst.Sat (fun x => x ∈ pool) → r ∈ S)

theorem checked_closed (rows S : List Row) (food pool : List Nat)
    (hraf : RAF S food) (h : checkClosed rows S food pool = true) : ClosedRAF rows S food := by
  have hh := of_decide_eq_true h
  change (∀ x ∈ food, x ∈ pool) ∧
    (∀ r ∈ S, (∀ x ∈ r.inputs, x ∈ pool) → ∀ y ∈ r.outputs, y ∈ pool) ∧
    (∀ r ∈ rows, (∀ x ∈ r.inputs, x ∈ pool) → r.catalyst.Sat (fun x => x ∈ pool) → r ∈ S) at hh
  have hg : ∀ x, Generated S food x → x ∈ pool := by
    intro x hx
    induction hx with
    | food hx => exact hh.1 _ hx
    | reaction r hr _ y hy ih => exact hh.2.1 r hr ih y hy
  refine ⟨hraf,?_⟩
  intro r hr hi hc
  exact hh.2.2 r hr (fun x hx => hg x (hi x hx)) (r.catalyst.sat_mono hg hc)

theorem raf_contains_seed {S : List Row} {food : List Nat} (h : RAF S food) :
    ∃ r ∈ S, ∀ x ∈ r.inputs, x ∈ food := by
  apply Classical.byContradiction
  intro hn
  have hgen : ∀ x, Generated S food x → x ∈ food := by
    intro x hx
    induction hx with
    | food hx => exact hx
    | reaction r hr _ y _ ih => exact False.elim (hn ⟨r,hr,ih⟩)
  cases S with
  | nil => exact h.1 rfl
  | cons r rs =>
    have hr : r ∈ r :: rs := List.mem_cons_self
    exact hn ⟨r,hr,fun x hx => hgen x ((h.2 r hr).1 x hx)⟩

theorem raf_of_same_rows {S T : List Row} {food : List Nat}
    (he : SameRows S T) (h : RAF S food) : RAF T food := by
  constructor
  · intro ht
    cases S with
    | nil => exact h.1 rfl
    | cons r rs =>
      have hr := he.1 r List.mem_cons_self
      simp [ht] at hr
  · intro r hr
    have hh := h.2 r (he.2 r hr)
    exact ⟨fun x hx => generated_mono he.1 (hh.1 x hx),
      r.catalyst.sat_mono (fun _ hx => generated_mono he.1 hx) hh.2⟩

theorem irreducible_of_singleton {S : List Row} {food : List Nat} {r : Row}
    (he : SameRows S [r]) (h : RAF [r] food) : Irreducible S food := by
  refine ⟨raf_of_same_rows ⟨he.2,he.1⟩ h,?_⟩
  intro T hT hraf s hs
  have hs' : s = r := by simpa using he.1 s hs
  cases T with
  | nil => exact False.elim (hraf.1 rfl)
  | cons t ts =>
    have ht : t = r := by simpa using he.1 t (hT t List.mem_cons_self)
    subst s
    subst t
    exact List.mem_cons_self

theorem catalogue_from_seeds (rows : List Row) (food : List Nat) (a b : Row)
    (hseeds : ∀ r ∈ rows, (∀ x ∈ r.inputs, x ∈ food) → r = a ∨ r = b)
    (ha : RAF [a] food) (hb : RAF [b] food)
    (S : List Row) (hsub : Subrows S rows) :
    Irreducible S food ↔ SameRows S [a] ∨ SameRows S [b] := by
  constructor
  · intro h
    obtain ⟨r,hr,hfood⟩ := raf_contains_seed h.1
    have hsing : Subrows [r] S := by
      intro s hs
      have he : s = r := by simpa using hs
      exact he ▸ hr
    rcases hseeds r (hsub r hr) hfood with he | he
    · subst r
      exact Or.inl ⟨h.2 [a] hsing ha,hsing⟩
    · subst r
      exact Or.inr ⟨h.2 [b] hsing hb,hsing⟩
  · intro h
    exact h.elim (fun he => irreducible_of_singleton he ha)
      (fun he => irreducible_of_singleton he hb)

end RAFBiochemicalLiteral

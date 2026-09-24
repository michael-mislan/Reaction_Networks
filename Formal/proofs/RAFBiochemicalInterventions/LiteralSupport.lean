import proofs.RAFBiochemicalInterventions.LiteralCertificates

namespace RAFBiochemicalLiteral

def Formula.Sat (P : Nat → Prop) : Formula → Prop
  | .atom x => P x
  | .both a b => a.Sat P ∧ b.Sat P
  | .either a b => a.Sat P ∨ b.Sat P
  | .yes => True

def satDecidable (pool : List Nat) : (f : Formula) → Decidable (f.Sat (fun x => x ∈ pool))
  | .atom x => inferInstanceAs (Decidable (x ∈ pool))
  | .both a b => @instDecidableAnd _ _ (satDecidable pool a) (satDecidable pool b)
  | .either a b => @instDecidableOr _ _ (satDecidable pool a) (satDecidable pool b)
  | .yes => isTrue True.intro

instance (pool : List Nat) (f : Formula) : Decidable (f.Sat (fun x => x ∈ pool)) :=
  satDecidable pool f

theorem Formula.sat_mono (f : Formula) {P Q : Nat → Prop}
    (h : ∀ x, P x → Q x) (hf : f.Sat P) : f.Sat Q := by
  induction f with
  | atom x => exact h x hf
  | both a b ha hb => exact ⟨ha hf.1,hb hf.2⟩
  | either a b ha hb => exact hf.elim (fun hx => Or.inl (ha hx)) (fun hx => Or.inr (hb hx))
  | yes => trivial

theorem generated_mono {S T : List Row} {food : List Nat}
    (h : ∀ r ∈ S, r ∈ T) {x : Nat} (hx : Generated S food x) : Generated T food x := by
  induction hx with
  | food hx => exact Generated.food hx
  | reaction r hr _ y hy ih => exact Generated.reaction r (h r hr) ih y hy

def RAF (S : List Row) (food : List Nat) : Prop :=
  S ≠ [] ∧ ∀ r ∈ S, (∀ x ∈ r.inputs, Generated S food x) ∧
    r.catalyst.Sat (Generated S food)

def Capable (rows : List Row) (food : List Nat) (p : Nat) : Prop :=
  ∃ S : List Row, (∀ r ∈ S, r ∈ rows) ∧ RAF S food ∧ Generated S food p

theorem capable_mono {S T : List Row} {food : List Nat} {p : Nat}
    (h : ∀ r ∈ S, r ∈ T) (hp : Capable S food p) : Capable T food p := by
  obtain ⟨U,hu,hraf,hp⟩ := hp
  exact ⟨U,fun r hr => h r (hu r hr),hraf,hp⟩

theorem not_capable_of_not_generated {rows : List Row} {food : List Nat} {p : Nat}
    (h : ¬ Generated rows food p) : ¬ Capable rows food p := by
  rintro ⟨S,hs,_,hp⟩
  exact h (generated_mono hs hp)

def supportStep (S : List Row) (pool : List Nat) (r : Row) : List Nat :=
  if r ∈ S ∧ ∀ x ∈ r.inputs, x ∈ pool then pool ++ r.outputs else pool

def replay (S : List Row) (pool : List Nat) : List Row → List Nat
  | [] => pool
  | r :: rs => replay S (supportStep S pool r) rs

theorem step_sound (S : List Row) (food pool : List Nat) (r : Row)
    (hp : ∀ x ∈ pool, Generated S food x) :
    ∀ x ∈ supportStep S pool r, Generated S food x := by
  unfold supportStep
  split
  next h =>
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hp x hx
    · exact Generated.reaction r h.1 (fun y hy => hp y (h.2 y hy)) x hx
  next => exact hp

theorem replay_sound (S : List Row) (food pool : List Nat) (order : List Row)
    (hp : ∀ x ∈ pool, Generated S food x) :
    ∀ x ∈ replay S pool order, Generated S food x := by
  induction order generalizing pool with
  | nil => exact hp
  | cons r rs ih => exact ih (supportStep S pool r) (step_sound S food pool r hp)

def checkSupport (rows : List Row) (food : List Nat) (S order : List Row) (p : Nat) : Bool :=
  let pool := replay S food order
  decide ((∀ r ∈ S, r ∈ rows) ∧ S ≠ [] ∧
    (∀ r ∈ S, (∀ x ∈ r.inputs, x ∈ pool) ∧ r.catalyst.Sat (fun x => x ∈ pool)) ∧ p ∈ pool)

theorem checked_support (rows : List Row) (food : List Nat) (S order : List Row) (p : Nat)
    (h : checkSupport rows food S order p = true) : Capable rows food p := by
  have hh := of_decide_eq_true h
  change (∀ r ∈ S, r ∈ rows) ∧ S ≠ [] ∧
    (∀ r ∈ S, (∀ x ∈ r.inputs, x ∈ replay S food order) ∧
      r.catalyst.Sat (fun x => x ∈ replay S food order)) ∧ p ∈ replay S food order at hh
  have hp := replay_sound S food food order (fun _ hx => Generated.food hx)
  refine ⟨S,hh.1,⟨hh.2.1,?_⟩,hp p hh.2.2.2⟩
  intro r hr
  exact ⟨fun x hx => hp x ((hh.2.2.1 r hr).1 x hx),
    r.catalyst.sat_mono hp (hh.2.2.1 r hr).2⟩

def restore (cut : List Nat) (a : Nat) : List Nat := cut.filter (fun b => b != a)

theorem remaining_antitone (rows : List Row) {D E : List Nat}
    (h : ∀ a ∈ D, a ∈ E) : ∀ r ∈ remaining rows E, r ∈ remaining rows D := by
  intro r hr
  have hh : r ∈ rows ∧ r.action ∉ E := by simpa [remaining] using hr
  have hout : r.action ∉ D := fun hx => hh.2 (h r.action hx)
  simpa [remaining] using And.intro hh.1 hout

def MinimalCut (rows : List Row) (food : List Nat) (p : Nat) (D : List Nat) : Prop :=
  ¬ Capable (remaining rows D) food p ∧
    ∀ E : List Nat, (∀ a ∈ E, a ∈ D) →
      ¬ Capable (remaining rows E) food p → ∀ a ∈ D, a ∈ E

theorem minimal_cut_of_restorations (rows : List Row) (food : List Nat)
    (p : Nat) (D : List Nat) (hfail : ¬ Capable (remaining rows D) food p)
    (hrestore : ∀ a ∈ D, Capable (remaining rows (restore D a)) food p) :
    MinimalCut rows food p D := by
  refine ⟨hfail,?_⟩
  intro E hE hfailE a ha
  apply Classical.byContradiction
  intro hn
  have hsub : ∀ b ∈ E, b ∈ restore D a := by
    intro b hb
    have hne : b ≠ a := fun he => hn (he ▸ hb)
    simpa [restore] using And.intro (hE b hb) hne
  exact hfailE (capable_mono (remaining_antitone rows hsub) (hrestore a ha))

end RAFBiochemicalLiteral

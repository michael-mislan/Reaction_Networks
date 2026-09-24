import proofs.RAFBiochemicalInterventions.RankedClosed

namespace RAFBiochemicalLiteral

theorem generated_has_producer {S : List Row} {food : List Nat} {x : Nat}
    (hx : Generated S food x) (hf : x ∉ food) : ∃ r ∈ S, x ∈ r.outputs := by
  cases hx with
  | food h => exact False.elim (hf h)
  | reaction r hr _ _ hy => exact ⟨r,hr,hy⟩

theorem unique_producer_forced (rows S : List Row) (food : List Nat) (x : Nat) (r : Row)
    (hs : Subrows S rows) (hf : x ∉ food)
    (hu : ∀ s ∈ rows, x ∈ s.outputs → s = r) (hx : Generated S food x) : r ∈ S := by
  obtain ⟨s,hs',hx'⟩ := generated_has_producer hx hf
  exact hu s (hs s hs') hx' ▸ hs'

def Formula.requires : Formula → Nat → Bool
  | .atom y, x => decide (x = y)
  | .both a b, x => a.requires x || b.requires x
  | .either a b, x => a.requires x && b.requires x
  | .yes, _ => false

theorem Formula.required (f : Formula) (P : Nat → Prop) (x : Nat)
    (h : f.requires x = true) (hs : f.Sat P) : P x := by
  induction f with
  | atom y => have he : x = y := of_decide_eq_true h; exact he ▸ hs
  | both a b ha hb =>
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact ha h hs.1
    · exact hb h hs.2
  | either a b ha hb =>
    have hh := Bool.and_eq_true_iff.mp h
    exact hs.elim (ha hh.1) (hb hh.2)
  | yes => contradiction

theorem input_forces (rows S : List Row) (food : List Nat) (r s : Row) (x : Nat)
    (hsub : Subrows S rows) (hraf : RAF S food) (hr : r ∈ S)
    (hi : x ∈ r.inputs) (hf : x ∉ food)
    (hu : ∀ t ∈ rows, x ∈ t.outputs → t = s) : s ∈ S :=
  unique_producer_forced rows S food x s hsub hf hu ((hraf.2 r hr).1 x hi)

theorem catalyst_forces (rows S : List Row) (food : List Nat) (r s : Row) (x : Nat)
    (hsub : Subrows S rows) (hraf : RAF S food) (hr : r ∈ S)
    (hi : r.catalyst.requires x = true) (hf : x ∉ food)
    (hu : ∀ t ∈ rows, x ∈ t.outputs → t = s) : s ∈ S :=
  unique_producer_forced rows S food x s hsub hf hu
    (r.catalyst.required _ x hi (hraf.2 r hr).2)

def prefixCheck : List Row → List Nat → Bool
  | [], _ => true
  | r :: rs, pool => r.inputs.all pool.contains && r.catalyst.test pool.contains &&
      prefixCheck rs (pool ++ r.outputs)

theorem prefix_forces (rows C : List Row) (food : List Nat) (hc : ClosedRAF rows C food)
    (order : List Row) (pool : List Nat) (hsub : Subrows order rows)
    (hp : ∀ x ∈ pool, Generated C food x) (h : prefixCheck order pool = true) :
    Subrows order C := by
  induction order generalizing pool with
  | nil => intro r hr; simp at hr
  | cons r rs ih =>
    have hh := Bool.and_eq_true_iff.mp h
    have hi := Bool.and_eq_true_iff.mp hh.1
    have hinputs : ∀ x ∈ r.inputs, Generated C food x := by
      intro x hx
      exact hp x (by simpa using List.all_eq_true.mp hi.1 x hx)
    have hcat := r.catalyst.sat_mono (fun x hx => hp x (by simpa using hx))
      ((r.catalyst.test_iff _).mp hi.2)
    have hr := hc.2 r (hsub r List.mem_cons_self) hinputs hcat
    have hpool : ∀ x ∈ pool ++ r.outputs, Generated C food x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hp x hx
      · exact Generated.reaction r hr hinputs x hx
    have hrest := ih (pool ++ r.outputs) (fun s hs => hsub s (List.mem_cons_of_mem r hs)) hpool hh.2
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he ▸ hr
    · exact hrest s hs

theorem outputs_generated (S : List Row) (food : List Nat) (h : RAF S food) :
    ∀ x ∈ S.flatMap Row.outputs, Generated S food x := by
  intro x hx
  obtain ⟨r,hr,hx⟩ := List.mem_flatMap.mp hx
  exact Generated.reaction r hr (h.2 r hr).1 x hx

end RAFBiochemicalLiteral

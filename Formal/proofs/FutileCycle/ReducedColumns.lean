import proofs.FutileCycle.IncidenceDeterminant
import proofs.FutileCycle.Source

namespace FutileCycle

def freeEmbed {S E C : Type*} : S ⊕ E → Species S E C :=
  Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)

def rowSign {S E : Type*} : S ⊕ E → ℤ := Sum.elim (fun _ => 1) (fun _ => -1)

def outgoing (b : Bool) : Direction := if b then .convert else .unbind

variable {S E C U V : Type*} [DecidableEq S] [DecidableEq E] [DecidableEq C]
    [Fintype V]

def reducedColumn (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (v : V → C) (d : V → Bool) (c : C) (i : U) : ℤ :=
  rowSign (f i) * (stoich N (freeEmbed (f i)) (c,.bind) +
    ∑ k, stoich N (freeEmbed (f i)) (v k, outgoing (d k)) *
      (if v k = c then 1 else 0))

theorem reducedColumn_unselected (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (v : V → C) (d : V → Bool) (c : C) (hc : ∀ k, v k ≠ c) (i : U) :
    reducedColumn N f v d c i =
      (if f i = .inr (N.enzyme c) then 1 else 0) -
      (if f i = .inl (N.input c) then 1 else 0) := by
  rcases hfi : f i with s | e <;>
    simp [reducedColumn, hc, hfi, rowSign, freeEmbed, stoich, product, reactant]
  split_ifs <;> norm_num

theorem reducedColumn_selected (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (v : V → C) (hv : Function.Injective v) (d : V → Bool) (k : V) (i : U) :
    reducedColumn N f v d (v k) i =
      (if f i = .inl (if d k then N.output (v k) else N.input (v k)) then 1 else 0) -
      (if f i = .inl (N.input (v k)) then 1 else 0) := by
  classical
  have hsum : (∑ l, stoich N (freeEmbed (f i)) (v l, outgoing (d l)) *
      (if v l = v k then 1 else 0)) =
      stoich N (freeEmbed (f i)) (v k, outgoing (d k)) := by
    rw [Fintype.sum_eq_single k]
    · simp
    · intro l hl
      simp [hv.ne hl]
  unfold reducedColumn
  rw [hsum]
  rcases f i with s | e <;> cases d k <;>
    simp [rowSign, freeEmbed, outgoing, stoich, product, reactant,
      sub_eq_add_neg, add_comm]

theorem reducedColumn_endpoints (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (v : V → C) (hv : Function.Injective v) (d : V → Bool) (c : C) :
    ∃ a b : S ⊕ E, ∀ i, reducedColumn N f v d c i =
      (if f i = a then 1 else 0) - (if f i = b then 1 else 0) := by
  classical
  by_cases hc : ∃ k, v k = c
  · obtain ⟨k, rfl⟩ := hc
    exact ⟨.inl (if d k then N.output (v k) else N.input (v k)),
      .inl (N.input (v k)), reducedColumn_selected N f v hv d k⟩
  · exact ⟨.inr (N.enzyme c), .inl (N.input c),
      reducedColumn_unselected N f v d c (by simpa using hc)⟩

theorem signedIncidence_of_endpoints {X I J : Type*} [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) (A : Matrix I J ℤ)
    (h : ∀ j, ∃ a b, ∀ i, A i j =
      (if f i = a then 1 else 0) - (if f i = b then 1 else 0)) :
    SignedIncidence A := by
  constructor
  · intro i j
    obtain ⟨a,b,h⟩ := h j
    rw [h i]
    split_ifs <;> norm_num
  constructor
  · intro j i k hi hk
    obtain ⟨a,b,h⟩ := h j
    have hi' : f i = a := by
      rw [h i] at hi
      split_ifs at hi <;> omega
    have hk' : f k = a := by
      rw [h k] at hk
      split_ifs at hk <;> omega
    exact hf (hi'.trans hk'.symm)
  · intro j i k hi hk
    obtain ⟨a,b,h⟩ := h j
    have hi' : f i = b := by
      rw [h i] at hi
      split_ifs at hi <;> omega
    have hk' : f k = b := by
      rw [h k] at hk
      split_ifs at hk <;> omega
    exact hf (hi'.trans hk'.symm)

theorem reducedColumns_signedIncidence (N : ConversionSystem S E C)
    (f : U → S ⊕ E) (hf : Function.Injective f)
    (v : V → C) (hv : Function.Injective v) (d : V → Bool) (b : U → C) :
    SignedIncidence (fun i j => reducedColumn N f v d (b j) i) := by
  exact signedIncidence_of_endpoints f hf _
    (fun j => reducedColumn_endpoints N f v hv d (b j))

end FutileCycle

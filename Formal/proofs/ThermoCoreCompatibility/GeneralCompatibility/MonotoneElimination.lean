import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

/-!
Exact elimination of one variable from a system of monotone two-variable
implications `z j ≥ f (z i)`.  This is the order-theoretic core of the
fixed-parameter algorithm: the projection of the feasible set is again a system
of monotone implications, obtained by composing the incoming maps, the
`next`-map of the admissible set of the eliminated variable, and the outgoing
maps.  No continuity, algebraicity or finiteness of pieces is used here; the
piece counts and the real-algebraic execution are conventional.
-/

namespace ThermoCoreCompatibility.GeneralCompatibility

/-- `ν` is a next-map of `U`: whenever `U` has a point at or above `a`,
`ν a` is the least such point. -/
def IsNextMap (U : Set ℝ) (ν : ℝ → ℝ) : Prop :=
  ∀ a, (∃ x ∈ U, a ≤ x) → ν a ∈ U ∧ a ≤ ν a ∧ ∀ x ∈ U, a ≤ x → ν a ≤ x

theorem IsNextMap.mono {U : Set ℝ} {ν : ℝ → ℝ} (hν : IsNextMap U ν)
    {a b : ℝ} (hab : a ≤ b) (hb : ∃ x ∈ U, b ≤ x) : ν a ≤ ν b := by
  obtain ⟨hbU, hbb, _⟩ := hν b hb
  have ha : ∃ x ∈ U, a ≤ x := ⟨ν b, hbU, hab.trans hbb⟩
  exact (hν a ha).2.2 (ν b) hbU (hab.trans hbb)

theorem IsNextMap.fixed_of_mem {U : Set ℝ} {ν : ℝ → ℝ} (hν : IsNextMap U ν)
    {a : ℝ} (ha : a ∈ U) : ν a = a := by
  obtain ⟨_, h1, h2⟩ := hν a ⟨a, ha, le_rfl⟩
  exact le_antisymm (h2 a ha le_rfl) h1

/-- Vertex elimination.  The eliminated variable ranges over `U` (its box
intersected with its self-constraint set), receives lower bounds `fin i (zi i)`
and the constant `l`, and sends lower bounds `fout j x` to the variables `zj j`.
If `a` is the largest incoming lower bound, a feasible value exists iff `U`
reaches above `a` and the least admissible value `ν a` satisfies every outgoing
implication. -/
theorem eliminate_vertex_iff {I J : Type*} {U : Set ℝ} {ν : ℝ → ℝ}
    (hν : IsNextMap U ν) (fin : I → ℝ → ℝ) (fout : J → ℝ → ℝ)
    (hout : ∀ j, Monotone (fout j)) (zi : I → ℝ) (zj : J → ℝ) (l a : ℝ)
    (hla : l ≤ a) (hia : ∀ i, fin i (zi i) ≤ a)
    (hleast : ∀ x, l ≤ x → (∀ i, fin i (zi i) ≤ x) → a ≤ x) :
    (∃ x ∈ U, l ≤ x ∧ (∀ i, fin i (zi i) ≤ x) ∧ ∀ j, fout j x ≤ zj j) ↔
      (∃ x ∈ U, a ≤ x) ∧ ∀ j, fout j (ν a) ≤ zj j := by
  constructor
  · rintro ⟨x, hxU, hlx, hix, hjx⟩
    have hax : a ≤ x := hleast x hlx hix
    refine ⟨⟨x, hxU, hax⟩, fun j => ?_⟩
    have hνx : ν a ≤ x := (hν a ⟨x, hxU, hax⟩).2.2 x hxU hax
    exact (hout j hνx).trans (hjx j)
  · rintro ⟨hex, hj⟩
    obtain ⟨hU, haν, _⟩ := hν a hex
    exact ⟨ν a, hU, hla.trans haν, fun i => (hia i).trans haν, hj⟩

/-- The least admissible value is the least feasible value of the eliminated
variable, so back-substitution of `ν a` reconstructs the least state. -/
theorem eliminated_value_least {I : Type*} {U : Set ℝ} {ν : ℝ → ℝ}
    (hν : IsNextMap U ν) (fin : I → ℝ → ℝ) (zi : I → ℝ) (l a : ℝ)
    (hleast : ∀ x, l ≤ x → (∀ i, fin i (zi i) ≤ x) → a ≤ x)
    {x : ℝ} (hxU : x ∈ U) (hlx : l ≤ x) (hix : ∀ i, fin i (zi i) ≤ x) :
    ν a ≤ x := by
  have hax : a ≤ x := hleast x hlx hix
  exact (hν a ⟨x, hxU, hax⟩).2.2 x hxU hax

/-- The generated implication between two remaining variables is monotone on
the set where the eliminated variable is still admissible. -/
theorem generated_map_mono {U : Set ℝ} {ν : ℝ → ℝ} (hν : IsNextMap U ν)
    {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) {x y : ℝ} (hxy : x ≤ y)
    (hy : ∃ u ∈ U, f y ≤ u) : g (ν (f x)) ≤ g (ν (f y)) :=
  hg (hν.mono (hf hxy) hy)

/-- The self-constraint set `{x | T x ≤ x}` of a monotone map is closed under
the operation used by the algorithm: its next-map fixes its points. -/
theorem self_constraint_next_fixed {T ν : ℝ → ℝ}
    (hν : IsNextMap {x | T x ≤ x} ν) {x : ℝ} (hx : T x ≤ x) : ν x = x :=
  hν.fixed_of_mem hx

end ThermoCoreCompatibility.GeneralCompatibility

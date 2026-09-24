import proofs.ThermoCoreCompatibility.Hypergraph.ShortcutPathRelaxations

namespace ThermoCoreCompatibility.Hypergraph.Shortcut
open scoped BigOperators

noncomputable def family (L : ℕ) (hL : 2 ≤ L) :
    CoreFamily (Core := Fin (L+1)) (assembly L hL).network where
  core := (assembly L hL).motif
  core_isPAC := (assembly L hL).source_isPAC
  orientation := fun _ => 1
  orientation_unit := fun _ => Or.inl rfl
  owner := Prod.fst
  owner_mem := by intro r; rcases r with ⟨e,(_|_)⟩ <;> simp [PairAssembly.motif]

noncomputable def complexValues (L : ℕ) (c : Complex (Fin (L+1))) : ℝ :=
  max (1/2) (if (∑ i, c i)=1 then ∑ i, (c i:ℝ)*activity L i
    else (∑ i, (c i:ℝ)*doubled L i)/2)

theorem complex_single (L : ℕ) (hL : 2 ≤ L) (i : Fin (L+1)) :
    complexValues L (atom i 1)=activity L i := by
  have h := (activity_bounds L hL i).1
  simp [complexValues,atom]
  linarith

theorem complex_double (L : ℕ) (hL : 2 ≤ L) (i : Fin (L+1)) :
    complexValues L (atom i 2)=doubled L i := by
  have h := ((scalar_relaxations L hL).2.1 i).1
  simp [complexValues,atom]
  linarith

theorem source_relaxed (L : ℕ) (hL : 2 ≤ L) : (family L hL).LinearComplexCompatible := by
  refine ⟨complexValues L,?_,?_,?_⟩
  · intro c
    exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_left _ _)
  · rintro ⟨e,(_|_)⟩
    all_goals
      have h := (scalar_relaxations L hL).2.2 e
      simp only [family,ReversibleCRN.linearCurrent,PairAssembly.network,Int.cast_one,one_mul,
        complex_single L hL,complex_double L hL]
    · linarith [h.1]
    · exact h.2.2.1
  · intro e
    rw [show (family L hL).core e=(assembly L hL).motif e from rfl,
      (assembly L hL).productive_iff]
    have h := (scalar_relaxations L hL).2.2 e
    simpa only [ReversibleCRN.linearCurrent,PairAssembly.network,one_mul,
      complex_single L hL,complex_double L hL] using h.2.2.2

theorem source_directions (L : ℕ) (hL : 2 ≤ L) :
    ∃ z : Fin (L+1) → ℝ, (∀ i, 9/10 ≤ z i ∧ z i ≤ 1) ∧
      ∀ r, 0 < (assembly L hL).network.current z r := by
  refine ⟨activity L,(scalar_relaxations L hL).1,?_⟩
  rintro ⟨e,(_|_)⟩
  all_goals
    have h := (scalar_relaxations L hL).2.2 e
    simp only [ReversibleCRN.current,PairAssembly.network,activity_atom,one_mul,pow_one]
  · exact sub_pos.mpr h.1
  · exact sub_pos.mpr h.2.1

/-- Unbounded source-valid minimal conflicts passing both physical directions
and one global independent-complex assignment. -/
theorem unbounded_monomial_order (L : ℕ) (hL : 2 ≤ L) :
    (∀ e, ((assembly L hL).motif e).IsPAC) ∧
    (¬ ∃ z : Fin (L+1) → ℝ, (∀ i, 0 < z i) ∧
      ∀ e, ((assembly L hL).motif e).Productive ((assembly L hL).network.current z)) ∧
    (∀ F, F ≠ Set.univ → Compatible L hL F) ∧
    (∃ z : Fin (L+1) → ℝ, (∀ i, 9/10 ≤ z i ∧ z i ≤ 1) ∧
      ∀ r, 0 < (assembly L hL).network.current z r) ∧
    (family L hL).LinearComplexCompatible ∧
    (∀ i, 9/10 ≤ complexValues L (atom i 1) ∧ complexValues L (atom i 1) ≤ 1) ∧
    (∀ i, 81/100 ≤ complexValues L (atom i 2) ∧ complexValues L (atom i 2) ≤ 1) := by
  refine ⟨(assembly L hL).source_isPAC,source_full_incompatible L hL,source_proper L hL,
    source_directions L hL,source_relaxed L hL,?_,?_⟩
  · simpa only [complex_single L hL] using (scalar_relaxations L hL).1
  · simpa only [complex_double L hL] using (scalar_relaxations L hL).2.1

end ThermoCoreCompatibility.Hypergraph.Shortcut

import proofs.ThermoCoreCompatibility.Hypergraph.PairResponseBounds

namespace ThermoCoreCompatibility.Hypergraph.Shortcut

def assembly (L : ℕ) (hL : 2 ≤ L) : PairAssembly (Fin (L+1)) (Fin (L+1)) where
  src e := if e.val < L then e else ⟨0,by omega⟩
  dst e := if h : e.val < L then ⟨e.val+1,by omega⟩ else ⟨L,by omega⟩
  distinct e := by
    dsimp
    split_ifs <;> intro h <;> have hh := congrArg Fin.val h <;> dsimp at hh <;> omega

def rank (L : ℕ) (j i : Fin (L+1)) : ℕ :=
  if j.val=L then i.val else if i.val ≤ j.val then L+i.val else i.val+1

theorem rank_bound (L : ℕ) (j i : Fin (L+1)) : rank L j i ≤ 2*L := by
  unfold rank
  split_ifs <;> omega

theorem rank_edge (L : ℕ) (hL : 2 ≤ L) (j e : Fin (L+1)) (he : e ≠ j) :
    rank L j ((assembly L hL).dst e) = rank L j ((assembly L hL).src e)+1 := by
  have hv : e.val ≠ j.val := fun h => he (Fin.ext h)
  simp only [assembly,rank]
  split_ifs <;> simp_all <;> omega

def Compatible (L : ℕ) (hL : 2 ≤ L) (F : Set (Fin (L+1))) : Prop :=
  ∃ z : Fin (L+1) → ℝ, (∀ i, 9/10 ≤ z i ∧ z i ≤ 1) ∧
    ∀ e ∈ F, ((assembly L hL).motif e).Productive ((assembly L hL).network.current z)

theorem source_deletion (L : ℕ) (hL : 2 ≤ L) (j : Fin (L+1)) :
    Compatible L hL {e | e ≠ j} := by
  refine ⟨fun i => Graded.state (2*L) (rank L j i),fun i => Graded.state_bounds _ _,?_⟩
  intro e he
  apply ((assembly L hL).current_productive_iff e _).2
  exact Graded.edge_productive (rank_bound L j _) (rank_edge L hL j e he)

theorem source_full_incompatible (L : ℕ) (hL : 2 ≤ L) :
    ¬ ∃ z : Fin (L+1) → ℝ, (∀ i, 0 < z i) ∧
      ∀ e, ((assembly L hL).motif e).Productive ((assembly L hL).network.current z) := by
  rintro ⟨z,hz,he⟩
  let x : ℕ → ℝ := fun i => if h : i < L+1 then z ⟨i,h⟩ else 1
  have hx : ∀ i ≤ L, 0 < x i := by
    intro i hi
    simp only [x,dif_pos (show i<L+1 by omega)]
    exact hz _
  have hp : ∀ i < L, Ring.Productive (x i) (x (i+1)) := by
    intro i hi
    have hh := ((assembly L hL).current_productive_iff ⟨i,by omega⟩ z).1 (he ⟨i,by omega⟩)
    simpa [assembly,hi,x,show i ≤ L by omega,show i<L+1 by omega,show i+1<L+1 by omega] using hh
  have hs := ((assembly L hL).current_productive_iff ⟨L,by omega⟩ z).1 (he ⟨L,by omega⟩)
  have hs' : Ring.Productive (x 0) (x L) := by
    simpa [assembly,x,show 0<L+1 by omega] using hs
  exact PairResponse.path_incompatible hL x hx hp hs'

theorem source_proper (L : ℕ) (hL : 2 ≤ L) (F : Set (Fin (L+1)))
    (hF : F ≠ Set.univ) : Compatible L hL F := by
  classical
  have hex : ∃ j, j ∉ F := by
    by_contra hh
    push Not at hh
    exact hF (Set.eq_univ_of_forall hh)
  obtain ⟨j,hj⟩ := hex
  obtain ⟨z,hb,hz⟩ := source_deletion L hL j
  exact ⟨z,hb,fun e he => hz e (by intro heq; subst e; exact hj he)⟩

theorem arbitrary_order (L : ℕ) (hL : 2 ≤ L) :
    (∀ e, ((assembly L hL).motif e).IsPAC) ∧
    (¬ ∃ z : Fin (L+1) → ℝ, (∀ i, 0 < z i) ∧
      ∀ e, ((assembly L hL).motif e).Productive ((assembly L hL).network.current z)) ∧
    ∀ F, F ≠ Set.univ → Compatible L hL F :=
  ⟨(assembly L hL).source_isPAC,source_full_incompatible L hL,source_proper L hL⟩

end ThermoCoreCompatibility.Hypergraph.Shortcut

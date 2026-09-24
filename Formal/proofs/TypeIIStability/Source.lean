import proofs.MixedDegradation.TypeIISource

namespace TypeIIStability.Source
open TypeIIL
open TypeIIL.PaperWeakStemSpecies
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def next6 : Fin 6 ≃ Fin 6 := finRotate 6
def back6 : Fin 6 → Option (Fin 6) := ![some 5, none, some 1, none, some 3, none]
def fork6 : Fin 3 ↪ Fin 6 := ⟨![0, 2, 4], by decide⟩
def stem6 : Fin 3 → Fin 6 := ![1, 3, 5]
def backStem6 : Fin 3 → Fin 6 := ![5, 1, 3]

def gap6 (j : Fin 3) : SourceGapEmbedding next6 back6 0 where
  idx := ⟨fun _ => stem6 j, by intro a b _; exact Fin.ext (by omega)⟩
  nonfork := by fin_cases j <;> decide
  successor_support := by fin_cases j <;> decide
  predecessor_support := by fin_cases j <;> decide
  no_two_cycle := by decide

def skeleton : SourceCyclicNonemptyGapSystem (l := 3) next6 back6 where
  step := finRotate 3
  cyclicOrder := Equiv.refl _
  step_cyclicOrder := by intro i; rfl
  fork := fork6
  gapLength := fun _ => 0
  gap := gap6
  wrap := by
    intro j
    refine { pre := ?_
             post := ?_
             right_successor_ne_left := ?_
             right_successor_ne_leftBack := ?_
             right_ne_leftBack := ?_ }
    · refine { terminal_next := ?_
               fork_back := ?_
               fork_successor_outside := ?_
               fork_ne_next := ?_ } <;> fin_cases j <;> decide
    · refine { first_eq := ?_
               fork_back := ?_
               fork_outside := ?_
               fork_not_successor := ?_
               back_outside := ?_
               back_not_successor := ?_ } <;>
        fin_cases j <;> decide
    all_goals fin_cases j <;> decide
  cover := by decide
  fork_ne_gap := by decide
  gap_owner := by decide

def weakGap : Fin 3 → Bool := fun _ => true
def vertex : Fin 6 → PaperWeakStemSpecies weakGap :=
  ![Sum.inl 0, Sum.inr ⟨0, rfl⟩, Sum.inl 1, Sum.inr ⟨1, rfl⟩,
    Sum.inl 2, Sum.inr ⟨2, rfl⟩]
def code : PaperWeakStemSpecies weakGap → Fin 6
  | Sum.inl j => fork6 j
  | Sum.inr j => stem6 j.val

theorem code_vertex (i : Fin 6) : code (vertex i) = i := by fin_cases i <;> rfl
theorem vertex_code (i : PaperWeakStemSpecies weakGap) : vertex (code i) = i := by
  rcases i with j | ⟨j, hj⟩ <;> fin_cases j <;> rfl

def edge6 (a b : Fin 6) : Prop :=
  b = next6 a ∨ (a = 0 ∧ b = 5) ∨ (a = 2 ∧ b = 1) ∨ (a = 4 ∧ b = 3)
instance (a b : Fin 6) : Decidable (edge6 a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem split_edge_code {a b : PaperWeakStemSpecies weakGap}
    (h : SplitEdge weakGap a b) : edge6 (code a) (code b) := by
  cases h with
  | main a =>
    left
    rcases a with j | ⟨j, hj⟩ <;> fin_cases j <;>
      decide +revert
  | back j =>
    fin_cases j <;>
      decide

def avoidSet : Fin 6 → Fin 3 → Finset (Fin 6) := ![![{1, 2, 3, 4, 5}, {3, 4, 5}, {5}],
    ![∅, {0, 3, 4, 5}, {0, 5}],
    ![{1}, {0, 1, 3, 4, 5}, {0, 1, 5}],
    ![{1, 2}, ∅, {0, 1, 2, 5}],
    ![{1, 2, 3}, {3}, {0, 1, 2, 3, 5}],
    ![{1, 2, 3, 4}, {3, 4}, ∅]]

theorem avoid_certificate : ∀ k j, fork6 j ≠ k → stem6 j ≠ k → backStem6 j ≠ k →
    stem6 j ∈ avoidSet k j ∧ backStem6 j ∉ avoidSet k j ∧
    ∀ a b, a ∈ avoidSet k j → edge6 a b → b ≠ k → b ∈ avoidSet k j := by decide

theorem weak_minimal : SourceMinimal weakGap := by
  rintro ⟨R⟩
  classical
  have hn : ∃ missing, missing ∉ R.species := by
    by_contra! h
    exact R.proper (Finset.eq_univ_of_forall h)
  obtain ⟨missing, hm⟩ := hn
  obtain ⟨j, hf, hs, hb⟩ := R.internalFork
  let k := code missing
  have havoid : ∀ a, a ∈ R.species → code a ≠ k := by
    intro a ha heq
    have : a = missing := by
      change code a = code missing at heq
      simpa only [vertex_code] using congrArg vertex heq
    exact hm (this ▸ ha)
  have hfc : code (fork weakGap j) = fork6 j := rfl
  have hsc : code (mainNext weakGap (fork weakGap j)) = stem6 j := by
    fin_cases j <;> rfl
  have hbc : code (backTarget weakGap j) = backStem6 j := by
    fin_cases j <;> rfl
  have hc := avoid_certificate k j
    (hfc ▸ havoid _ hf) (hsc ▸ havoid _ hs) (hbc ▸ havoid _ hb)
  have hpath := R.stronglyConnected hs hb
  have hpres : ∀ {a b}, Relation.ReflTransGen (RestrictedEdge weakGap R.species) a b →
      code a ∈ avoidSet k j → code b ∈ avoidSet k j := by
    intro a b hp
    induction hp with
    | refl => exact id
    | @tail b c hp he ih =>
      intro ha
      exact hc.2.2 _ _ (ih ha) (split_edge_code he.2.2) (havoid _ he.2.1)
  exact hc.2.1 (hbc ▸ hpres hpath (hsc.symm ▸ hc.1))

def walk (a : Fin 6) : ℕ → Fin 6
  | 0 => a
  | n+1 => next6 (walk a n)

theorem vertex_next (i : Fin 6) : mainNext weakGap (vertex i) = vertex (next6 i) := by
  fin_cases i <;> rfl

theorem walk_reachable (a : Fin 6) (n : ℕ) :
    Relation.ReflTransGen (RestrictedEdge weakGap Finset.univ) (vertex a) (vertex (walk a n)) := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    apply ih.tail
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
    rw [walk, ← vertex_next]
    exact SplitEdge.main _

theorem weak_top : MixedDegradation.TypeII.PaperRaw.SourceTop weakGap where
  stronglyConnected := by
    intro a b
    have hc : ∀ i j : Fin 6, ∃ n : Fin 6, walk i n.val = j := by decide
    obtain ⟨n, hn⟩ := hc (code a) (code b)
    simpa only [hn, vertex_code] using walk_reachable (code a) n.val
  internalFork := ⟨0, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _⟩

end TypeIIStability.Source

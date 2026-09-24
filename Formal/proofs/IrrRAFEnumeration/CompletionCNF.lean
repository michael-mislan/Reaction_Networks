import proofs.IrrRAFEnumeration.FiniteDuality

namespace IrrRAFEnumeration

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A truth assignment represented by its true variables satisfies the exact
completion CNF: every input edge is hit, while no already known minimal
transversal is contained in it. -/
def CompletionWitness (H G : Finset (Finset α)) (S : Finset α) : Prop :=
  Hits H S ∧ ∀ A ∈ G, ¬ A ⊆ S

omit [DecidableEq α] in
/-- The exact global-certificate formulation of completion.  A supplied
subfamily of minimal transversals is incomplete iff the monotone CNF with
positive clauses `H` and negative clauses `G` has a satisfying assignment. -/
theorem missing_minimalTransversal_iff_completionWitness
    (H G : Finset (Finset α)) (hG : G ⊆ blocker H) :
    (∃ A, A ∈ blocker H ∧ A ∉ G) ↔
      ∃ S, CompletionWitness H G S := by
  classical
  constructor
  · rintro ⟨A, hAH, hAG⟩
    refine ⟨A, (mem_blocker.mp hAH).1, ?_⟩
    intro B hBG hBA
    have hBH : B ∈ blocker H := hG hBG
    have hAB : A ⊆ B := (mem_blocker.mp hAH).2 (mem_blocker.mp hBH).1 hBA
    exact hAG (Finset.Subset.antisymm hAB hBA ▸ hBG)
  · rintro ⟨S, hSH, havoid⟩
    obtain ⟨A, hAS, hAmin⟩ := exists_minimal_subset (Hits H) hSH
    refine ⟨A, mem_blocker.mpr hAmin, ?_⟩
    intro hAG
    exact havoid A hAG hAS

/-- A flip set renames the completion CNF to Horn exactly when every positive
clause has at most one unflipped variable and every negative clause has at
most one flipped variable. -/
def CompletionHornFlip (H G : Finset (Finset α)) (F : Finset α) : Prop :=
  (∀ E ∈ H, (E \ F).card ≤ 1) ∧
    ∀ A ∈ G, (A ∩ F).card ≤ 1

omit [Fintype α] in
theorem minimal_hits_iff_oneDeletion (H : Finset (Finset α)) (A : Finset α) :
    Minimal (Hits H) A ↔
      Hits H A ∧ ∀ x ∈ A, ¬ Hits H (A.erase x) := by
  constructor
  · intro hmin
    refine ⟨hmin.1, ?_⟩
    intro x hxA herase
    have hAerase : A ⊆ A.erase x :=
      hmin.2 herase (A.erase_subset x)
    have : x ∈ A.erase x := hAerase hxA
    simp at this
  · rintro ⟨hA, hdelete⟩
    refine ⟨hA, ?_⟩
    intro B hB hBA
    change B ⊆ A at hBA
    by_contra hAB
    change ¬ A ⊆ B at hAB
    rw [Finset.not_subset] at hAB
    obtain ⟨x, hxA, hxB⟩ := hAB
    have hBerase : B ⊆ A.erase x := by
      intro y hyB
      exact Finset.mem_erase.mpr ⟨by
        intro hyx
        exact hxB (hyx ▸ hyB), hBA hyB⟩
    exact hdelete x hxA (hits_mono hBerase hB)

def hornCounterexampleH : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2}, {1, 2}, {0, 3}, {1, 3}}

def hornCounterexampleG : Finset (Finset (Fin 4)) :=
  {{0, 1}, {0, 2, 3}}

/-- The four-vertex preflight instance is legitimate: the supplied sets are
minimal transversals of the positive input hypergraph. -/
theorem hornCounterexampleG_minimal :
    ∀ A ∈ hornCounterexampleG, Minimal (Hits hornCounterexampleH) A := by
  simp [minimal_hits_iff_oneDeletion, Hits, hornCounterexampleG,
    hornCounterexampleH]

/-- The third displayed set is a genuine missing minimal transversal. -/
theorem hornCounterexample_missing :
    Minimal (Hits hornCounterexampleH) {1, 2, 3} ∧
      {1, 2, 3} ∉ hornCounterexampleG := by
  rw [minimal_hits_iff_oneDeletion]
  constructor
  · simp [Hits, hornCounterexampleH]
  · native_decide

/-- The exact completion CNF need not be renamable Horn, already on four
vertices. -/
theorem hornCounterexample_not_renamable :
    ¬ ∃ F, CompletionHornFlip hornCounterexampleH hornCounterexampleG F := by
  rintro ⟨F, hpos, hneg⟩
  have h01 := hpos {0, 1} (by simp [hornCounterexampleH])
  have h02 := hpos {0, 2} (by simp [hornCounterexampleH])
  have h03 := hpos {0, 3} (by simp [hornCounterexampleH])
  have h13 := hpos {1, 3} (by simp [hornCounterexampleH])
  have hn01 := hneg {0, 1} (by simp [hornCounterexampleG])
  have hn023 := hneg {0, 2, 3} (by simp [hornCounterexampleG])
  by_cases h0 : (0 : Fin 4) ∈ F
  · have h2 : (2 : Fin 4) ∉ F := by
      intro h2
      have heq := (Finset.card_le_one.mp hn023) 0 (by simp [h0]) 2 (by simp [h2])
      omega
    have h3 : (3 : Fin 4) ∉ F := by
      intro h3
      have heq := (Finset.card_le_one.mp hn023) 0 (by simp [h0]) 3 (by simp [h3])
      omega
    have h1 : (1 : Fin 4) ∈ F := by
      by_contra h1
      have heq := (Finset.card_le_one.mp h13) 1 (by simp [h1]) 3 (by simp [h3])
      omega
    have heq := (Finset.card_le_one.mp hn01) 0 (by simp [h0]) 1 (by simp [h1])
    omega
  · have h1 : (1 : Fin 4) ∈ F := by
      by_contra h1
      have heq := (Finset.card_le_one.mp h01) 0 (by simp [h0]) 1 (by simp [h1])
      omega
    have h2 : (2 : Fin 4) ∈ F := by
      by_contra h2
      have heq := (Finset.card_le_one.mp h02) 0 (by simp [h0]) 2 (by simp [h2])
      omega
    have h3 : (3 : Fin 4) ∈ F := by
      by_contra h3
      have heq := (Finset.card_le_one.mp h03) 0 (by simp [h0]) 3 (by simp [h3])
      omega
    have heq := (Finset.card_le_one.mp hn023) 2 (by simp [h2]) 3 (by simp [h3])
    omega

end IrrRAFEnumeration

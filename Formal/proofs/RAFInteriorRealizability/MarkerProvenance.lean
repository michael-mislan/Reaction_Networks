import proofs.RAFInteriorRealizability.MarkerSource

namespace RAFInteriorRealizability

open RAF RAF.Frankl MarkerMolecule

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

namespace MarkerSource

theorem marker_origin (A : AntimatroidData E) (S : Finset E)
    {target : E} {B : Finset E} {k : Nat}
    (h : marker target B ∈ closureAt (crs A) S k) :
    A.toUnionClosedData.IsBlocker target B ∧ ∃ e ∈ B, e ∈ S := by
  classical
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hfood | ⟨e, heS, hout⟩
  · simp [crs] at hfood
  · simp [crs] at hout
    exact ⟨hout.1, e, hout.2, heS⟩

theorem catalyst_origin (A : AntimatroidData E) (S : Finset E)
    {e : E} {k : Nat} (h : catalyst e ∈ closureAt (crs A) S k) : e ∈ S := by
  classical
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hfood | ⟨u, huS, hout⟩
  · simp [crs] at hfood
  · simp [crs] at hout
    simpa [hout] using huS

theorem marker_reachable_of_hit (A : AntimatroidData E) {S : Finset E}
    (hfg : FoodGenerated (crs A) S) {target e : E} {B : Finset E}
    (heS : e ∈ S) (heB : e ∈ B)
    (hB : A.toUnionClosedData.IsBlocker target B) :
    ∃ k, marker target B ∈ closureAt (crs A) S k := by
  apply output_mem_some_closureAt_of_foodGenerated (crs A) hfg heS
  classical
  simp [crs, hB, heB]

theorem closureAt_subset_succ (A : AntimatroidData E) (S : Finset E) (k : Nat) :
    closureAt (crs A) S k ⊆ closureAt (crs A) S (k + 1) := by
  intro x hx
  simp only [closureAt, closureStep, Finset.mem_union]
  exact Or.inl hx

theorem closureAt_mono_time (A : AntimatroidData E) (S : Finset E)
    {j k : Nat} (hjk : j ≤ k) :
    closureAt (crs A) S j ⊆ closureAt (crs A) S k := by
  induction k, hjk using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ k _ ih => exact Finset.Subset.trans ih (closureAt_subset_succ A S k)

theorem finite_inputs_reach_one_stage (A : AntimatroidData E) (S : Finset E)
    (T : Finset (MarkerMolecule E))
    (hT : ∀ x ∈ T, ∃ k, x ∈ closureAt (crs A) S k) :
    ∃ k, T ⊆ closureAt (crs A) S k := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x T hxT ih =>
      obtain ⟨j, hxj⟩ := hT x (Finset.mem_insert_self x T)
      obtain ⟨k, hTk⟩ := ih (fun y hy => hT y (Finset.mem_insert_of_mem hy))
      refine ⟨max j k, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hyT
      · exact closureAt_mono_time A S (Nat.le_max_left j k) hxj
      · exact closureAt_mono_time A S (Nat.le_max_right j k) (hTk hyT)

end MarkerSource

end RAFInteriorRealizability

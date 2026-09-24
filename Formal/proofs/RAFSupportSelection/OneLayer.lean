import proofs.RAFSupportSelection.SelectedCone

namespace RAFSupportSelection.OneLayer
open RAF RAF.Frankl RAFQueryCompilation

variable {P C : Type*} [DecidableEq P] [DecidableEq C] [Fintype P] [Fintype C]

def parents (choice : C → P) : P ⊕ C → Finset (P ⊕ C)
  | .inl _ => ∅
  | .inr c => {Sum.inl (choice c)}

def region (choice : C → P) (K : Finset (P ⊕ C)) : Finset (P ⊕ C) :=
  K ∪ Finset.univ.filter (fun r => (match r with
    | .inl _ => false
    | .inr c => decide (Sum.inl (choice c) ∈ K)) = true)

theorem cone_eq_region (choice : C → P) (K : Finset (P ⊕ C)) :
    selectedCone Finset.univ (parents choice) K = region choice K := by
  apply Finset.Subset.antisymm
  · apply selectedCone_le
    · intro r hr
      exact Finset.mem_union_left _ (Finset.mem_inter.mp hr).1
    · intro r _ hh
      cases r with
      | inl a => simp [parents] at hh
      | inr c =>
        obtain ⟨t, ht⟩ := hh
        obtain ⟨htp, htB⟩ := Finset.mem_inter.mp ht
        have he : t = Sum.inl (choice c) := by simpa [parents] using htp
        subst t
        have hk : Sum.inl (choice c) ∈ K := by simpa [region] using htB
        exact Finset.mem_union_right _ (by simp [hk])
  · intro r hr
    rcases Finset.mem_union.mp hr with hk | hr
    · exact selectedCone_seed _ _ _ (by simp [hk])
    · cases r with
      | inl a => simp at hr
      | inr c =>
        have hk : Sum.inl (choice c) ∈ K := by simpa using hr
        have hc := selectedCone_seed Finset.univ (parents choice) K
          (Finset.mem_inter.mpr ⟨hk, Finset.mem_univ _⟩)
        rw [← selectedCone_fixed Finset.univ (parents choice) K]
        apply Finset.mem_union_right
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨Sum.inl (choice c), by simp [parents, hc]⟩

def ancestors (choice : C → P) (r : P ⊕ C) : Finset (P ⊕ C) :=
  Finset.univ.filter (fun k => r ∈ selectedCone Finset.univ (parents choice) {k})

theorem ancestors_producer (choice : C → P) (a : P) :
    ancestors choice (Sum.inl a) = {Sum.inl a} := by
  ext k
  cases k <;> simp [ancestors, cone_eq_region, region]
  exact eq_comm

theorem ancestors_consumer (choice : C → P) (c : C) :
    ancestors choice (Sum.inr c) = {Sum.inr c, Sum.inl (choice c)} := by
  ext k
  cases k <;> simp [ancestors, cone_eq_region, region] <;> exact eq_comm

/-- Integer workload weights; uniform singleton cost is obtained with every weight one
and division by the number of reactions. -/
def cost (w : P ⊕ C → ℕ) (choice : C → P) : ℕ :=
  ∑ r : P ⊕ C, ∑ k ∈ ancestors choice r, w k

theorem cost_formula (w : P ⊕ C → ℕ) (choice : C → P) :
    cost w choice = (∑ a : P, w (Sum.inl a)) +
      (∑ c : C, w (Sum.inr c)) + ∑ c : C, w (Sum.inl (choice c)) := by
  simp [cost, Fintype.sum_sum_type, ancestors_producer, ancestors_consumer,
    Finset.sum_add_distrib, Nat.add_assoc]

/-- The actual pointwise-minimum selection solves the whole weighted reachability
objective on the one-layer assignment class, not merely an edge-count surrogate. -/
theorem minimum_weight_optimal (w : P ⊕ C → ℕ) (allowed : C → Finset P)
    (choice : C → P)
    (hmin : ∀ c a, a ∈ allowed c → w (Sum.inl (choice c)) ≤ w (Sum.inl a))
    (other : C → P) (ho : ∀ c, other c ∈ allowed c) :
    cost w choice ≤ cost w other := by
  rw [cost_formula, cost_formula]
  exact Nat.add_le_add_left (Finset.sum_le_sum (fun c _ => hmin c (other c) (ho c))) _

end RAFSupportSelection.OneLayer

import proofs.RAFQueryCompilation.RestrictionReuse

namespace RAFQueryCompilation
open RAF

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- No nonfood output of the edited region is needed by an outside reaction. -/
def OutsideIndependent (Q : CRS M R) (C : Catalysis M R) (E : Finset R) : Prop :=
  ∀ e ∈ E, ∀ r, r ∉ E → ∀ x ∈ Q.outputs e,
    (x ∈ Q.inputs r ∨ C x r) → x ∈ Q.food

def Protected (Q : CRS M R) (E : Finset R) (x : M) : Prop :=
  ∀ e ∈ E, x ∈ Q.outputs e → x ∈ Q.food

omit [DecidableEq R] in
theorem food_subset_closureAt (Q : CRS M R) (S : Finset R) (k : ℕ) :
    Q.food ⊆ closureAt Q S k := by
  induction k with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact ih.trans Finset.subset_union_left

omit [DecidableEq R] in
theorem outside_input_protected (Q : CRS M R) (C : Catalysis M R)
    {E : Finset R} (h : OutsideIndependent Q C E) {r : R} (hr : r ∉ E)
    {x : M} (hx : x ∈ Q.inputs r) : Protected Q E x := by
  intro e he ho
  exact h e he r hr x ho (Or.inl hx)

omit [DecidableEq R] in
theorem outside_catalyst_protected (Q : CRS M R) (C : Catalysis M R)
    {E : Finset R} (h : OutsideIndependent Q C E) {r : R} (hr : r ∉ E)
    {x : M} (hx : C x r) : Protected Q E x := by
  intro e he ho
  exact h e he r hr x ho (Or.inr hx)

/-- Protected molecular derivations survive removal of the entire edited region. -/
theorem protected_closure_projection (Q : CRS M R) (C : Catalysis M R)
    {E : Finset R} (hind : OutsideIndependent Q C E) (S : Finset R) (k : ℕ) :
    ∀ x, Protected Q E x → x ∈ closureAt Q S k → x ∈ closureAt Q (S \ E) k := by
  induction k with
  | zero => intro x _ hx; exact hx
  | succ k ih =>
      intro x hp hx
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
      rcases hx with hx | ⟨r, hr, hx⟩
      · exact Or.inl (ih x hp hx)
      · by_cases hen : Enabled Q (closureAt Q S k) r
        · have ho : x ∈ Q.outputs r := by simpa [hen] using hx
          by_cases he : r ∈ E
          · exact Or.inl (food_subset_closureAt Q (S \ E) k (hp r he ho))
          · have en : Enabled Q (closureAt Q (S \ E) k) r := by
              intro y hy
              exact ih y (outside_input_protected Q C hind he hy) (hen hy)
            exact Or.inr ⟨r, Finset.mem_sdiff.mpr ⟨hr, he⟩, by simpa [en] using ho⟩
        · simp [hen] at hx

theorem outside_projection_isRAF (Q : CRS M R) (C : Catalysis M R)
    {E S : Finset R} (hind : OutsideIndependent Q C E) (hraf : IsRAF Q C S)
    (hne : (S \ E).Nonempty) : IsRAF Q C (S \ E) := by
  refine ⟨hne, ?_, ?_⟩
  · intro r hr
    obtain ⟨hrs, hre⟩ := Finset.mem_sdiff.mp hr
    obtain ⟨k, hk⟩ := hraf.2.1 r hrs
    refine ⟨k, fun x hx => ?_⟩
    exact protected_closure_projection Q C hind S k x
      (outside_input_protected Q C hind hre hx) (hk hx)
  · intro r hr
    obtain ⟨hrs, hre⟩ := Finset.mem_sdiff.mp hr
    obtain ⟨x, k, hx, hc⟩ := hraf.2.2 r hrs
    exact ⟨x, k, protected_closure_projection Q C hind S k x
      (outside_catalyst_protected Q C hind hre hc) hx, hc⟩

theorem evaluate_outside [Fintype M] (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] {E : Finset R} (hind : OutsideIndependent Q C E)
    (A : Finset R) : evaluate Q C A \ E = evaluate Q C (A \ E) := by
  apply Finset.Subset.antisymm
  · by_cases hn : (evaluate Q C A \ E).Nonempty
    · have ha : (evaluate Q C A).Nonempty := by
        obtain ⟨r, hr⟩ := hn
        exact ⟨r, (Finset.mem_sdiff.mp hr).1⟩
      have hr := (RAF.Frankl.isRAF_iff_nonempty_prune_eq Q C _).mpr
        ⟨ha, evaluate_fixed Q C A⟩
      apply raf_subset_evaluate Q C _ (outside_projection_isRAF Q C hind hr hn)
      intro r hr
      exact Finset.mem_sdiff.mpr
        ⟨evaluate_subset Q C A (Finset.mem_sdiff.mp hr).1, (Finset.mem_sdiff.mp hr).2⟩
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  · intro r hr
    exact Finset.mem_sdiff.mpr
      ⟨evaluate_mono Q C Finset.sdiff_subset hr,
        (Finset.mem_sdiff.mp (evaluate_subset Q C (A \ E) hr)).2⟩

theorem outside_unchanged [Fintype M] (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] {E : Finset R} (hind : OutsideIndependent Q C E)
    {A B : Finset R} (hab : A \ E = B \ E) :
    evaluate Q C A \ E = evaluate Q C B \ E := by
  rw [evaluate_outside Q C hind A, evaluate_outside Q C hind B, hab]

end RAFQueryCompilation

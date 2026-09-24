import proofs.RAFReactionCriticality.CatalyticModules

namespace RAFReactionCriticality.CatalyticModules
open RAF RAFQueryCompilation FunctionalSource FiniteThinning
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J] (length : J → ℕ)

noncomputable local instance propositionDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def FullBlock (j : J) (mask : Reaction length → Bool) : Prop :=
  ∀ x : ZMod (length j+1), mask ⟨j,x⟩ = true

omit [DecidableEq J] in
theorem module_retained_iff (j : J) (mask : Reaction length → Bool) :
    moduleSet length j ⊆ available mask ↔ FullBlock length j mask := by
  constructor
  · intro h x
    have hm : (⟨j,x⟩ : Reaction length) ∈ moduleSet length j :=
      Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_filter.mp (h hm)).2
  · intro h r hr
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x⟩

theorem modular_nonempty_iff (mask : Reaction length → Bool) :
    (evaluate source (catalysts (parent length)) (available mask)).Nonempty ↔
      ∃ j, FullBlock length j mask := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r.1, (module_retained_iff length r.1 mask).mp ?_⟩
    rw [← orbit_eq_module]
    exact (safe_iff_orbit_subset _ _ _).mp ((evaluate_iff_orbit _ _ _).mp hr)
  · rintro ⟨j,hj⟩
    refine ⟨⟨j,0⟩, (evaluate_iff_orbit _ _ _).mpr ?_⟩
    apply (safe_iff_orbit_subset _ _ _).mpr
    rw [orbit_eq_module]
    exact (module_retained_iff length j mask).mpr hj

omit [Fintype J] [DecidableEq J] in
theorem local_failure_sum (j : J) (p : ℝ) :
    (∑ mask : ZMod (length j+1) → Bool,
      if ∀ x, mask x = true then 0 else weight p mask) = 1-p^(length j+1) := by
  classical
  have hc := contains_probability p (Finset.univ : Finset (ZMod (length j+1)))
  have ht := weight_sum (R := ZMod (length j+1)) p
  have hs : (∑ mask : ZMod (length j+1) → Bool,
      if ∀ x, mask x = true then 0 else weight p mask) =
      (∑ mask : ZMod (length j+1) → Bool, weight p mask) -
        probability p (Contains (Finset.univ : Finset (ZMod (length j+1)))) := by
    unfold probability
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro mask _
    by_cases h : ∀ x, mask x = true <;> simp [Contains, h]
  rw [hs, ht, hc]
  simp [ZMod.card]

omit [DecidableEq J] in
theorem failure_weight_factorization (p : ℝ) (m : (j : J) → ZMod (length j+1) → Bool) :
    (if ¬ ∃ j, FullBlock length j
        ((Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm m)
      then weight p ((Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm m)
      else 0) = ∏ j, (if ∀ x, m j x = true then (0 : ℝ) else weight p (m j)) := by
  classical
  by_cases h : ∃ j, ∀ x, m j x = true
  · have he : ∃ j, FullBlock length j
        ((Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm m) := h
    rw [if_neg (not_not.mpr he)]
    obtain ⟨j,hj⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_pos hj)
  · have he : ¬ ∃ j, FullBlock length j
        ((Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm m) := h
    rw [if_pos he]
    unfold weight
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro j _
    have hj : ¬ ∀ x, m j x = true := fun hj => h ⟨j,hj⟩
    rw [if_neg hj]
    rfl

theorem no_module_probability (p : ℝ) :
    probability p (fun mask : Reaction length → Bool => ¬ ∃ j, FullBlock length j mask) =
      ∏ j, (1-p^(length j+1)) := by
  classical
  unfold probability
  rw [← (Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm.sum_comp]
  calc
    _ = ∑ m : (j : J) → ZMod (length j+1) → Bool,
        ∏ j, (if ∀ x, m j x = true then (0 : ℝ) else weight p (m j)) :=
      by
        apply Finset.sum_congr rfl
        intro m _
        dsimp only
        have ht := failure_weight_factorization length p m
        by_cases h : ∃ j, FullBlock length j
          ((Equiv.piCurry (fun j (_ : ZMod (length j+1)) => Bool)).symm m)
        · simpa only [h, not_true_eq_false, if_false] using ht
        · simpa only [h, not_false_eq_true, if_true] using ht
    _ = ∏ j, ∑ m : ZMod (length j+1) → Bool,
        (if ∀ x, m x = true then (0 : ℝ) else weight p m) :=
      (Fintype.prod_sum (fun (j : J) (m : ZMod (length j+1) → Bool) =>
        if ∀ x, m x = true then (0 : ℝ) else weight p m)).symm
    _ = _ := by simp_rw [local_failure_sum]

/-- Exact nonempty survival curve for arbitrary finite catalytic-module lengths. -/
theorem survival_probability (p : ℝ) :
    probability p (fun mask : Reaction length → Bool =>
      (evaluate source (catalysts (parent length)) (available mask)).Nonempty) =
      1 - ∏ j, (1-p^(length j+1)) := by
  classical
  have ht : probability p (fun mask : Reaction length → Bool =>
        (evaluate source (catalysts (parent length)) (available mask)).Nonempty) +
      probability p (fun mask : Reaction length → Bool => ¬ ∃ j, FullBlock length j mask) = 1 := by
    unfold probability
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ mask : Reaction length → Bool, weight p mask := by
        apply Finset.sum_congr rfl
        intro mask _
        dsimp only
        simp only [modular_nonempty_iff]
        by_cases h : ∃ j, FullBlock length j mask <;> simp [h]
      _ = 1 := weight_sum p
  rw [no_module_probability] at ht
  linarith

end RAFReactionCriticality.CatalyticModules

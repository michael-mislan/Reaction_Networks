import proofs.RAFReactionCriticality.FunctionalSource
import proofs.RAFReactionCriticality.CatalystChoice
import proofs.RAFReactionCriticality.FiniteThinning

namespace RAFReactionCriticality
open RAF RAFQueryCompilation
open FunctionalSource FiniteThinning
variable {R : Type*} [Fintype R] [DecidableEq R]

noncomputable def orbitSet (f : R → R) (r : R) : Finset R := by
  classical
  exact Finset.univ.filter (fun t => ∃ k : ℕ, f^[k] r = t)

omit [DecidableEq R] in
theorem safe_iff_orbit_subset (f : R → R) (r : R) (A : Finset R) :
    Safe f A r ↔ orbitSet f r ⊆ A := by
  classical
  constructor
  · intro h t ht
    obtain ⟨k, rfl⟩ := (Finset.mem_filter.mp ht).2
    exact h k
  · intro h k
    exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, rfl⟩)

def available (mask : R → Bool) : Finset R := Finset.univ.filter (fun r => mask r)

omit [DecidableEq R] in
theorem orbit_subset_available (f : R → R) (r : R) (mask : R → Bool) :
    orbitSet f r ⊆ available mask ↔ Contains (orbitSet f r) mask := by
  simp [Finset.subset_iff, available, Contains]

/-- Exact all-intervention law on interacting cycles and branches with one redundant site. -/
theorem redundant_orbit_law (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (A : Finset R) (r : R) :
    r ∈ evaluate source (fun x t => catalysts f x t ∨ catalysts g x t) A ↔
      orbitSet f r ⊆ A ∨ orbitSet g r ⊆ A := by
  rw [evaluate_one_site_choice source (catalysts f) (catalysts g) v
    (fun t ht x => by simp only [catalysts, h t ht])]
  simp only [Finset.mem_union, evaluate_iff_orbit, safe_iff_orbit_subset]

/-- The two branch witnesses retain their literal overlap under one frozen source. -/
theorem redundant_target_probability (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (r : R) (p : ℝ) :
    probability p (fun mask => r ∈ evaluate source
      (fun x t => catalysts f x t ∨ catalysts g x t) (available mask)) =
      p^(orbitSet f r).card + p^(orbitSet g r).card -
        p^(orbitSet f r ∪ orbitSet g r).card := by
  simp_rw [redundant_orbit_law f g v h, orbit_subset_available]
  exact two_witness_probability p _ _

/-- A singleton deletion is fatal to a target precisely in the shared exposure set. -/
theorem redundant_singleton_loss (f g : R → R) (v : R)
    (h : ∀ r, r ≠ v → f r = g r) (r t : R) :
    r ∉ evaluate source (fun x s => catalysts f x s ∨ catalysts g x s)
      (Finset.univ \ {t}) ↔ t ∈ orbitSet f r ∩ orbitSet g r := by
  classical
  rw [redundant_orbit_law f g v h]
  simp only [not_or, Finset.subset_sdiff, Finset.subset_univ, true_and,
    Finset.disjoint_singleton_right, not_not, Finset.mem_inter]

end RAFReactionCriticality

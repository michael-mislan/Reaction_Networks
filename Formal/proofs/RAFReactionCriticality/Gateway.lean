import proofs.RAFReactionCriticality.Main

namespace RAFReactionCriticality
open RAF RAFQueryCompilation FunctionalSource FiniteThinning
variable {R : Type*} [Fintype R] [DecidableEq R]

theorem gateway_nonempty_iff (root : R) (A : Finset R) :
    (evaluate source (catalysts (fun _ => root)) A).Nonempty ↔ root ∈ A := by
  rw [evaluate_nonempty_iff]
  constructor
  · rintro ⟨S, hs, hf⟩
    obtain ⟨hne, hp⟩ := (raf_iff (fun _ => root) S).mp hf
    obtain ⟨r, hr⟩ := hne
    exact hs (hp r hr)
  · intro hr
    refine ⟨{root}, Finset.singleton_subset_iff.mpr hr, ?_⟩
    apply (raf_iff (fun _ => root) {root}).mpr
    simp

/-- Arbitrarily large literal sources whose RAF survival curve never sharpens. -/
theorem gateway_survival_probability (root : R) (p : ℝ) :
    probability p (fun mask =>
      (evaluate source (catalysts (fun _ => root)) (available mask)).Nonempty) = p := by
  have he : (fun mask =>
      (evaluate source (catalysts (fun _ => root)) (available mask)).Nonempty) =
      Contains ({root} : Finset R) := by
    funext mask
    apply propext
    rw [gateway_nonempty_iff]
    simp [available, Contains]
  rw [he, contains_probability]
  simp

end RAFReactionCriticality

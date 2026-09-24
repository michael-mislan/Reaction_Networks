import proofs.RAF.Frankl.CoreAbundance

namespace RAF.Frankl
open RAF
open scoped Classical BigOperators

variable {M R : Type*} [DecidableEq M] [Fintype R] [DecidableEq R]

/-- A nonempty food-ready set with internal or food support is a viable core.
In particular, the vertex set of a directed catalytic cycle meets this premise. -/
theorem supported_food_ready_abundant (Q : CRS M R) (C : Catalysis M R)
    (U : Finset R) (hne : U.Nonempty)
    (hE : ∀ r ∈ U, SeedReaction Q r)
    (hC : ProductGraphCatalyzed Q C U) :
    ∃ r ∈ U, (fixedFamily Q C).card ≤
      2 * ((fixedFamily Q C).filter (fun W => r ∈ W)).card := by
  apply elementary_core_exists_abundant Q C U ?_ hE
  apply (isRAF_iff_foodGenerated_and_productGraph Q C U).mpr
  exact ⟨hne, fun r hr => ⟨0, hE r hr⟩, hC⟩

/-- Disjoint viable elementary cores have distinct global abundance witnesses. -/
theorem disjoint_elementary_cores_distinct_abundant
    {I : Type*} [Fintype I] (Q : CRS M R) (C : Catalysis M R)
    (U : I → Finset R) (hU : ∀ i, IsRAF Q C (U i))
    (hE : ∀ i r, r ∈ U i → SeedReaction Q r)
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    ∃ f : I → R, Function.Injective f ∧ ∀ i,
      f i ∈ U i ∧ (fixedFamily Q C).card ≤
        2 * ((fixedFamily Q C).filter (fun W => f i ∈ W)).card := by
  classical
  choose f hf ha using fun i => elementary_core_exists_abundant Q C (U i) (hU i) (hE i)
  refine ⟨f, ?_, fun i => ⟨hf i, ha i⟩⟩
  intro i j hij
  by_contra hne
  exact Finset.disjoint_left.mp (hdis i j hne) (hf i) (hij ▸ hf i |> fun _ => by
    rw [hij]
    exact hf j)

/-- Real nonnegative weights on exterior contexts preserve the fibre inequality.
The inner family is exactly the selected core subsets in that context. -/
theorem exterior_weighted_fibre_average
    (Q : CRS M R) (C : Catalysis M R) (U : Finset R)
    (hU : IsRAF Q C U) (hE : ∀ r ∈ U, SeedReaction Q r)
    (contexts : Finset (Finset R)) (h : Finset R → ℝ)
    (hh : ∀ T ∈ contexts, 0 ≤ h T) :
    0 ≤ ∑ T ∈ contexts, h T *
      (2 * (∑ S ∈ extensionFibre Q C U T, (S.card : ℝ)) -
        (extensionFibre Q C U T).card * (Fintype.card {r // r ∈ U} : ℝ)) := by
  apply Finset.sum_nonneg
  intro T hT
  apply mul_nonneg (hh T hT)
  have hn := extensionFibre_average Q C U T hU hE
  have hr : ((extensionFibre Q C U T).card : ℝ) *
      (Fintype.card {r // r ∈ U} : ℝ) ≤
      2 * (∑ S ∈ extensionFibre Q C U T, (S.card : ℝ)) := by
    exact_mod_cast hn
  linarith

end RAF.Frankl

import proofs.RAFQueryCompilation.DependencyCone

namespace RAFQueryCompilation
open RAF
variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Producer multiplicities can be maintained using only removed/added reactions. -/
theorem producer_count_delta (Q : CRS M R) (S T : Finset R) (x : M) :
    producerCount Q T x = producerCount Q S x - producerCount Q (S \ T) x +
      producerCount Q (T \ S) x := by
  have hs := producer_count_partition Q S T x
  have ht := producer_count_partition Q T S x
  rw [Finset.inter_comm T S] at ht
  omega

def updateProducerCache (Q : CRS M R) (counts : M → ℕ) (removed added : Finset R) :
    M → ℕ := fun x => counts x - producerCount Q removed x + producerCount Q added x

theorem updateProducerCache_correct (Q : CRS M R) (S T : Finset R) (counts : M → ℕ)
    (hc : ∀ x, counts x = producerCount Q S x) :
    ∀ x, updateProducerCache Q counts (S \ T) (T \ S) x = producerCount Q T x := by
  intro x
  rw [updateProducerCache, hc x, producer_count_delta Q S T x]

variable [Fintype M]

def foodFromCache (Q : CRS M R) (C : Catalysis M R) [∀ x r, Decidable (C x r)]
    (oldAnswer E : Finset R) (counts : M → ℕ) : Finset M :=
  Q.food ∪ (neededSet Q C E).filter
    (fun x => producerCount Q (oldAnswer ∩ E) x < counts x)

theorem foodFromCache_eq (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (S E : Finset R) (counts : M → ℕ)
    (hc : ∀ x, counts x = producerCount Q S x) :
    foodFromCache Q C S E counts = cachedFood Q C S E := by
  simp only [foodFromCache, cachedFood, hc]

def cachedRegionUpdate (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (oldAnswer B E : Finset R) (counts : M → ℕ) : Finset R :=
  (oldAnswer \ E) ∪ evaluate (withFood Q (foodFromCache Q C oldAnswer E counts)) C (B ∩ E)

/-- Both the next answer and the producer-cache invariant are preserved. -/
theorem cachedRegionUpdate_correct (Q : CRS M R) (C : Catalysis M R)
    [∀ x r, Decidable (C x r)] (A B E : Finset R) (counts : M → ℕ)
    (hc : ∀ x, counts x = producerCount Q (evaluate Q C A) x)
    (hind : OutsideIndependent Q C E) (hab : A \ E = B \ E) :
    let old := evaluate Q C A
    let next := cachedRegionUpdate Q C old B E counts
    next = evaluate Q C B ∧
      ∀ x, updateProducerCache Q counts (old \ next) (next \ old) x =
        producerCount Q (evaluate Q C B) x := by
  dsimp only
  have hnext : cachedRegionUpdate Q C (evaluate Q C A) B E counts = evaluate Q C B := by
    rw [cachedRegionUpdate, foodFromCache_eq Q C _ E counts hc]
    exact (evaluate_cached_cone_update Q C A B E hind hab).symm
  refine ⟨hnext, ?_⟩
  rw [hnext]
  exact updateProducerCache_correct Q _ _ counts hc

end RAFQueryCompilation

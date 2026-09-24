import proofs.RAF.Frankl.PairGadget
import proofs.RAFQueryCompilation.Pruning

namespace RAF.Frankl.PairGadget
open RAF RAFQueryCompilation PairReaction
open scoped Classical

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Available coordinates require both reactions of the pair, not just a producer. -/
noncomputable def completePairs (T : Finset (PairReaction U)) : Finset U :=
  Finset.univ.filter fun i => producer i ∈ T ∧ gate i ∈ T

@[simp] theorem mem_completePairs (T : Finset (PairReaction U)) (i : U) :
    i ∈ completePairs T ↔ producer i ∈ T ∧ gate i ∈ T := by
  simp [completePairs]

theorem encode_subset_iff (A : Finset U) (T : Finset (PairReaction U)) :
    encode A ⊆ T ↔ A ⊆ completePairs T := by
  constructor
  · intro h i hi
    exact (mem_completePairs T i).mpr ⟨h ((producer_mem_encode A i).mpr hi),
      h ((gate_mem_encode A i).mpr hi)⟩
  · intro h r hr
    cases r with
    | producer i => exact ((mem_completePairs T i).mp (h ((producer_mem_encode A i).mp hr))).1
    | gate i => exact ((mem_completePairs T i).mp (h ((gate_mem_encode A i).mp hr))).2

/-- Uniform operator formula for arbitrary availability, including incomplete
pairs. The left side is the inherited executable maxRAF evaluator. -/
theorem evaluate_eq_encode_interior (D : UnionClosedData U)
    (T : Finset (PairReaction U)) :
    evaluate (crs D) catalysis T = encode (D.interior (completePairs T)) := by
  apply Finset.Subset.antisymm
  · intro r hr
    obtain ⟨S,hs,hraf,hrs⟩ := (evaluate_mem_iff (crs D) catalysis T r).mp hr
    have he := encode_decode_of_isRAF D hraf
    have ha : decode S ∈ D.family :=
      ((encoded_isRAF_iff_mem D (decode S)).mp (by rwa [he])).2
    have hc : decode S ⊆ completePairs T := (encode_subset_iff _ T).mp (by rwa [he])
    have hr' : r ∈ encode (decode S) := by rwa [he]
    cases r with
    | producer i =>
      exact (producer_mem_encode _ i).mpr ((D.mem_interior _ i).mpr
        ⟨decode S,ha,hc,(producer_mem_encode _ i).mp hr'⟩)
    | gate i =>
      exact (gate_mem_encode _ i).mpr ((D.mem_interior _ i).mpr
        ⟨decode S,ha,hc,(gate_mem_encode _ i).mp hr'⟩)
  · intro r hr
    have hs : encode (D.interior (completePairs T)) ⊆ T :=
      (encode_subset_iff _ T).mpr (D.interior_subset _)
    have hn : (D.interior (completePairs T)).Nonempty := by
      cases r with
      | producer i => exact ⟨i,(producer_mem_encode _ i).mp hr⟩
      | gate i => exact ⟨i,(gate_mem_encode _ i).mp hr⟩
    exact raf_subset_evaluate (crs D) catalysis hs
      ((encoded_isRAF_iff_mem D _).mpr ⟨hn,D.interior_mem _⟩) hr

/-- Deleting the mate of an available reaction removes that reaction from maxRAF. -/
theorem incomplete_pair_excluded (D : UnionClosedData U)
    (T : Finset (PairReaction U)) (i : U) :
    (gate i ∉ T → producer i ∉ evaluate (crs D) catalysis T) ∧
    (producer i ∉ T → gate i ∉ evaluate (crs D) catalysis T) := by
  rw [evaluate_eq_encode_interior]
  constructor
  · intro hg hp
    exact hg ((mem_completePairs T i).mp
      (D.interior_subset _ ((producer_mem_encode _ i).mp hp))).2
  · intro hp hg
    exact hp ((mem_completePairs T i).mp
      (D.interior_subset _ ((gate_mem_encode _ i).mp hg))).1

end RAF.Frankl.PairGadget

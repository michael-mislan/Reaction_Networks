import proofs.RAFQueryCompilation.MaskedRankedWitness
import proofs.RAFQueryCompilation.MaskedPruning

namespace RAFQueryCompilation
open RAF RAF.Frankl

theorem ranked_available_maximum {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (h : checkRankedSupport Q cats A parents rank = true) :
    evaluate Q (fun x r => x ∈ cats r) A = A := by
  have hf := ranked_retained_fixed Q cats A A parents rank
    (checkRankedSupport_sound Q cats A parents rank h) (Finset.Subset.refl A)
    (by intro r hr; exact Finset.inter_subset_right)
  apply Finset.Subset.antisymm (evaluate_subset Q _ A)
  by_cases he : A = ∅
  · simp [he]
  · exact raf_subset_evaluate Q _ (Finset.Subset.refl A)
      ((isRAF_iff_nonempty_prune_eq Q _ A).mpr ⟨Finset.nonempty_iff_ne_empty.mpr he,hf⟩)

/-- A witness for all available reactions certifies the maximum directly.
Rejected or incomplete witnesses take the established exact evaluator. -/
def rankedStartup {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ) : Finset (Fin m) × Bool :=
  let mask := patchVector (Vector.replicate m false) A (fun _ => true)
  if checkMaskedRankedSupport Q cats (fun r => mask[r.val]) parents rank then
    (A,true)
  else (maskedFreshEvaluate Q cats A,false)

theorem rankedStartup_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ) :
    (rankedStartup Q cats A parents rank).1 = evaluate Q (fun x r => x ∈ cats r) A := by
  unfold rankedStartup
  dsimp only
  split
  next h =>
    apply (ranked_available_maximum Q cats A parents rank _).symm
    apply checkMaskedRankedSupport_sound Q cats _ A parents rank _ h
    intro r
    simp [patchVector_get]
  next => exact maskedFreshEvaluate_correct Q cats A

theorem rankedStartup_accepted {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (A : Finset (Fin m))
    (parents : Fin m → Finset (Fin m)) (rank : Fin m → ℕ)
    (h : (rankedStartup Q cats A parents rank).2 = true) :
    checkRankedSupport Q cats (rankedStartup Q cats A parents rank).1 parents rank = true := by
  unfold rankedStartup at h ⊢
  dsimp only at h ⊢
  split
  next hc =>
    apply checkMaskedRankedSupport_sound Q cats _ A parents rank _ hc
    intro r
    simp [patchVector_get]
  next hc => simp [hc] at h

end RAFQueryCompilation

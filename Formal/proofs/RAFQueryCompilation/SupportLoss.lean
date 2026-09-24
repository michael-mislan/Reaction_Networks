import proofs.RAFQueryCompilation.RankedLoss
import proofs.RAFQueryCompilation.SupportPruning

namespace RAFQueryCompilation
open RAF

/-- A global support-certificate route for deletion regions too large to replay locally. -/
def supportLossTotal {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : QueryState n m) (D : Finset (Fin m))
    (cert : List (SupportRound m)) : Finset (Fin m) × Bool :=
  let available := freshAvailable state D ∅
  match checkSupportPruning Q cats available cert with
  | some answer => (maskSet state.answer \ answer, true)
  | none => (maskSet state.answer \ (freshEvaluate Q cats available).1, false)

theorem supportLossTotal_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (state : QueryState n m) (A D : Finset (Fin m))
    (ho : ∀ r, state.answer[r.val] = true ↔ r ∈ evaluate Q (fun x r => x ∈ cats r) A)
    (ha : ∀ r, state.available[r.val] = true ↔ r ∈ A)
    (cert : List (SupportRound m)) :
    (supportLossTotal Q cats state D cert).1 =
      evaluate Q (fun x r => x ∈ cats r) A \ evaluate Q (fun x r => x ∈ cats r) (A \ D) := by
  have hm : maskSet state.answer = evaluate Q (fun x r => x ∈ cats r) A := by
    ext r
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and, ho]
  have hav : freshAvailable state D ∅ = A \ D := by
    rw [freshAvailable_correct state A D ∅ ha, Finset.union_empty]
  unfold supportLossTotal
  rw [hav]
  cases hs : checkSupportPruning Q cats (A \ D) cert with
  | none => simp only [hs, hm, freshEvaluate_refines]
  | some answer =>
    have he := checkSupportPruning_sound Q cats cert (A \ D) hs
    simp only [hs, hm, he]

end RAFQueryCompilation

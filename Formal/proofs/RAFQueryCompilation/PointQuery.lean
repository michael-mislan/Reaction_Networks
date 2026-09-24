import proofs.RAFQueryCompilation.FreshQuery

namespace RAFQueryCompilation
open RAF

structure PointStep (m : ℕ) where
  members : List Bool
  available : Vector Bool m
  charge : ℕ

def pointPatchCharge {m : ℕ} (removed added : Finset (Fin m)) : ℕ :=
  let d := removed.card+added.card
  1+(d+1)^2+d*(added.card+1)

/-- Fresh membership service: no answer vector or producer-count cache is rebuilt. -/
def freshPointQuery {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (available : Vector Bool m)
    (removed added : Finset (Fin m)) (probes : List (Fin m)) : PointStep m :=
  let B := Finset.univ.filter (fun r => editedMask (fun s => available[s.val]) removed added r)
  let answer := freshEvaluate Q cats B
  { members := probes.map (fun r => decide (r ∈ answer.1))
    available := patchVector available (removed ∪ added) (fun r => decide (r ∈ added))
    charge := freshMaskCharge removed added+answer.2+pointPatchCharge removed added+
      probes.length*(answer.1.card+1) }

theorem freshPointQuery_correct {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (available : Vector Bool m)
    (A removed added : Finset (Fin m)) (probes : List (Fin m))
    (ha : ∀ r, available[r.val] = true ↔ r ∈ A) :
    (freshPointQuery Q cats available removed added probes).members =
      probes.map (fun r => decide (r ∈ evaluate Q (fun x r => x ∈ cats r) ((A \ removed) ∪ added))) ∧
    (∀ r, (freshPointQuery Q cats available removed added probes).available[r.val] = true ↔
      r ∈ (A \ removed) ∪ added) := by
  have hB : Finset.univ.filter (fun r => editedMask (fun s => available[s.val]) removed added r) =
      (A \ removed) ∪ added := by
    ext r
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      editedMask_correct (fun s => available[s.val]) A removed added ha r
  constructor
  · simp only [freshPointQuery,freshEvaluate_refines,hB]
  · exact fun r => patchAvailability_correct available A removed added ha r

theorem freshPointQuery_reads {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (available : Vector Bool m)
    (removed added : Finset (Fin m)) (probes : List (Fin m)) :
    m ≤ (freshPointQuery Q cats available removed added probes).charge := by
  have h : m ≤ m*(removed.card+added.card+3) := Nat.le_mul_of_pos_right _ (by omega)
  dsimp only [freshPointQuery,freshMaskCharge]
  omega

end RAFQueryCompilation

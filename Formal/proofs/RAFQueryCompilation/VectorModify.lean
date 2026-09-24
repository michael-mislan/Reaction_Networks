import proofs.RAFQueryCompilation.VectorPatch

namespace RAFQueryCompilation

/-- Transform each listed cell using its current value, without retaining the old array. -/
def modifyList {α : Type*} {n : ℕ} (v : Vector α n) (indices : List (Fin n))
    (change : Fin n → α → α) : Vector α n :=
  indices.foldl (fun acc i => acc.set i.val (change i acc[i.val]) i.isLt) v

theorem modifyList_get {α : Type*} {n : ℕ} (v : Vector α n) (indices : List (Fin n))
    (change : Fin n → α → α) (hnd : indices.Nodup) (i : Fin n) :
    (modifyList v indices change)[i.val] =
      if i ∈ indices then change i v[i.val] else v[i.val] := by
  induction indices generalizing v with
  | nil => rfl
  | cons r rs ih =>
    have hn := List.nodup_cons.mp hnd
    simp only [modifyList, List.foldl_cons] at ih ⊢
    rw [ih _ hn.2]
    by_cases hm : i ∈ rs
    · have he : r ≠ i := fun h => hn.1 (h.symm ▸ hm)
      have hv : r.val ≠ i.val := fun h => he (Fin.ext h)
      simp only [hm, List.mem_cons, or_true, if_true,
        Vector.getElem_set_ne r.isLt i.isLt hv]
    · by_cases he : r = i
      · subst r
        simp only [hm, List.mem_cons, true_or, if_true, if_false, Vector.getElem_set_self]
      · have hv : r.val ≠ i.val := fun h => he (Fin.ext h)
        have hi : i ≠ r := Ne.symm he
        simp only [hm, List.mem_cons, hi, or_self, if_false,
          Vector.getElem_set_ne r.isLt i.isLt hv]

def modifyVector {α : Type*} {n : ℕ} (v : Vector α n) (indices : Finset (Fin n))
    (change : Fin n → α → α) : Vector α n := modifyList v (indices.sort (· ≤ ·)) change

theorem modifyVector_get {α : Type*} {n : ℕ} (v : Vector α n) (indices : Finset (Fin n))
    (change : Fin n → α → α) (i : Fin n) :
    (modifyVector v indices change)[i.val] =
      if i ∈ indices then change i v[i.val] else v[i.val] := by
  rw [modifyVector, modifyList_get v _ change (Finset.sort_nodup _ _) i]
  simp only [Finset.mem_sort]

end RAFQueryCompilation

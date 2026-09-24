import proofs.RAFQueryCompilation.ReferenceEdits

namespace RAFQueryCompilation

def patchList {α : Type*} {n : ℕ} (v : Vector α n) (indices : List (Fin n))
    (value : Fin n → α) : Vector α n :=
  indices.foldl (fun acc i => acc.set i.val (value i) i.isLt) v

theorem patchList_get {α : Type*} {n : ℕ} (v : Vector α n) (indices : List (Fin n))
    (value : Fin n → α) (i : Fin n) :
    (patchList v indices value)[i.val] = if i ∈ indices then value i else v[i.val] := by
  induction indices generalizing v with
  | nil => rfl
  | cons r rs ih =>
    simp only [patchList, List.foldl_cons] at ih ⊢
    rw [ih]
    by_cases hm : i ∈ rs
    · simp only [hm, List.mem_cons, or_true, if_true]
    · by_cases he : r = i
      · subst r
        simp only [hm, List.mem_cons, true_or, if_true, if_false, Vector.getElem_set_self]
      · have hv : r.val ≠ i.val := fun h => he (Fin.ext h)
        simp only [hm, List.mem_cons, if_false, Vector.getElem_set_ne r.isLt i.isLt hv]
        have hi : i ≠ r := Ne.symm he
        simp only [hi, or_self, if_false]

def patchVector {α : Type*} {n : ℕ} (v : Vector α n) (indices : Finset (Fin n))
    (value : Fin n → α) : Vector α n := patchList v (indices.sort (· ≤ ·)) value

theorem patchVector_get {α : Type*} {n : ℕ} (v : Vector α n) (indices : Finset (Fin n))
    (value : Fin n → α) (i : Fin n) :
    (patchVector v indices value)[i.val] = if i ∈ indices then value i else v[i.val] := by
  simp only [patchVector, patchList_get, Finset.mem_sort]

end RAFQueryCompilation

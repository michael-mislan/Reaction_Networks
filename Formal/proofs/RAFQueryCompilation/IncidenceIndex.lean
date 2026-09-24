import proofs.RAFQueryCompilation.SparseCertificate
import proofs.RAFQueryCompilation.VectorModify

namespace RAFQueryCompilation
open RAF

def addConsumer {n m : ℕ} (needs : Fin m → Finset (Fin n))
    (table : Vector (Finset (Fin m)) n) (r : Fin m) : Vector (Finset (Fin m)) n :=
  modifyVector table (needs r) (fun _ row => insert r row)

def consumerRows {n m : ℕ} (needs : Fin m → Finset (Fin n)) :
    List (Fin m) → Vector (Finset (Fin m)) n → Vector (Finset (Fin m)) n
  | [], table => table
  | r::rest, table => consumerRows needs rest (addConsumer needs table r)

theorem consumerRows_mem {n m : ℕ} (needs : Fin m → Finset (Fin n))
    (order : List (Fin m)) (table : Vector (Finset (Fin m)) n) (x : Fin n) (r : Fin m) :
    r ∈ (consumerRows needs order table)[x.val] ↔
      r ∈ table[x.val] ∨ (r ∈ order ∧ x ∈ needs r) := by
  induction order generalizing table with
  | nil => simp [consumerRows]
  | cons s rest ih =>
    simp only [consumerRows, ih, addConsumer, modifyVector_get, List.mem_cons]
    by_cases hx : x ∈ needs s
    · simp only [hx, if_true, Finset.mem_insert]
      by_cases hr : r = s
      · subst r; simp [hx]
      · simp [hr]
    · simp only [hx, if_false]
      by_cases hr : r = s
      · subst r; simp [hx]
      · simp [hr]

def sourceConsumers {n m : ℕ} (needs : Fin m → Finset (Fin n)) : Vector (Finset (Fin m)) n :=
  consumerRows needs (Finset.univ.sort (· ≤ ·)) (Vector.replicate n ∅)

theorem sourceConsumers_mem {n m : ℕ} (needs : Fin m → Finset (Fin n))
    (x : Fin n) (r : Fin m) : r ∈ (sourceConsumers needs)[x.val] ↔ x ∈ needs r := by
  simp [sourceConsumers, consumerRows_mem]

def incidenceNeeds {n m : ℕ} (Q : CRS (Fin n) (Fin m)) (cats : Fin m → Finset (Fin n))
    (r : Fin m) : Finset (Fin n) := Q.inputs r ∪ cats r

def incidenceSuccessors {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (consumers : Vector (Finset (Fin m)) n) (e : Fin m) : Finset (Fin m) :=
  ((Q.outputs e) \ Q.food).biUnion (fun x => consumers[x.val])

theorem incidenceNeeds_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) :
    NeedsSound Q (fun x r => x ∈ cats r) (incidenceNeeds Q cats) := by
  intro r x h
  exact Finset.mem_union.mpr h

theorem incidenceSuccessors_eq {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) (e : Fin m) :
    incidenceSuccessors Q (sourceConsumers (incidenceNeeds Q cats)) e =
      sourceSuccessors Q (fun x r => x ∈ cats r) e := by
  ext r
  simp only [incidenceSuccessors, Finset.mem_biUnion, Finset.mem_sdiff,
    sourceConsumers_mem, incidenceNeeds, Finset.mem_union, sourceSuccessors,
    Finset.mem_filter, Finset.mem_univ, true_and]
  aesop

theorem incidenceSuccessors_sound {n m : ℕ} (Q : CRS (Fin n) (Fin m))
    (cats : Fin m → Finset (Fin n)) :
    IndexSound Q (fun x r => x ∈ cats r)
      (incidenceSuccessors Q (sourceConsumers (incidenceNeeds Q cats))) := by
  intro e r x hx hf hn
  rw [incidenceSuccessors_eq]
  exact sourceSuccessors_sound Q (fun x r => x ∈ cats r) e r x hx hf hn

end RAFQueryCompilation

import proofs.IrrRAFEnumeration.CircuitSource

namespace AllIrrRAFCert.Hardness

open RAF RAF.Frankl

abbrev Vertex (k n : Nat) := Fin k × Fin (n + 2)
abbrev Pair (k n : Nat) := Vertex k n × Vertex k n

inductive Mol (k n : Nat)
  | food
  | signal (v : Vertex k n)
  | guardCat (v : Vertex k n)
  | colorOK (i : Fin k)
  | pairOK (e : Pair k n)
  | globalCat
  deriving DecidableEq, Fintype

inductive Rxn (k n : Nat)
  | selector (v : Vertex k n)
  | colorGate (v : Vertex k n)
  | pairLeft (e : Pair k n)
  | pairRight (e : Pair k n)
  | close
  deriving DecidableEq, Fintype

variable {k n : Nat}

def next (v : Vertex k n) : Vertex k n :=
  (v.1, IrrRAFEnumeration.CircuitSource.nextAux v.2)

/-- True marks a forbidden pair; graph encoding supplies cross-color nonedges. -/
def crs (bad : Pair k n → Bool) : CRS (Mol k n) (Rxn k n) where
  food := {.food}
  inputs
    | .selector _ => {.food}
    | .colorGate v => (Finset.univ.erase v.2).image (fun w => .signal (v.1,w))
    | .pairLeft e => if bad e then {.signal e.1} else {.food}
    | .pairRight e => if bad e then {.signal e.2} else {.food}
    | .close => (Finset.univ.image Mol.colorOK) ∪ (Finset.univ.image Mol.pairOK)
  outputs
    | .selector v => {.signal v, .guardCat v}
    | .colorGate v => {.colorOK v.1}
    | .pairLeft e => {.pairOK e}
    | .pairRight e => {.pairOK e}
    | .close => {.globalCat}

def cat : Catalysis (Mol k n) (Rxn k n)
  | .globalCat, _ => True
  | .guardCat u, .selector v => u = next v
  | _, _ => False

def guard (i : Fin k) : Finset (Rxn k n) :=
  Finset.univ.image (fun w => Rxn.selector (i,w))

@[simp] theorem selector_mem_guard (i : Fin k) (v : Vertex k n) :
    Rxn.selector v ∈ guard i ↔ v.1 = i := by
  simp [guard, Prod.ext_iff, eq_comm]

@[simp] theorem close_not_mem_guard (i : Fin k) :
    Rxn.close ∉ guard (n := n) i := by simp [guard]

theorem signal_origin (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    {v : Vertex k n} {t : Nat} (h : Mol.signal v ∈ closureAt (crs bad) S t) :
    Rxn.selector v ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs bad) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    subst_vars
    exact hr

theorem guardCat_origin (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    {v : Vertex k n} {t : Nat} (h : Mol.guardCat v ∈ closureAt (crs bad) S t) :
    Rxn.selector v ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs bad) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    subst_vars
    exact hr

theorem globalCat_origin (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    {t : Nat} (h : Mol.globalCat ∈ closureAt (crs bad) S t) : Rxn.close ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs bad) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    exact hr

theorem colorOK_origin (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    {i : Fin k} {t : Nat} (h : Mol.colorOK i ∈ closureAt (crs bad) S t) :
    ∃ w, Rxn.colorGate (i,w) ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs bad) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r with
    | selector v => simp [crs] at ho
    | colorGate v =>
      simp [crs] at ho
      exact ⟨v.2, by simpa [ho] using hr⟩
    | pairLeft e => simp [crs] at ho
    | pairRight e => simp [crs] at ho
    | close => simp [crs] at ho

theorem pairOK_origin (bad : Pair k n → Bool) (S : Finset (Rxn k n))
    {e : Pair k n} {t : Nat} (h : Mol.pairOK e ∈ closureAt (crs bad) S t) :
    Rxn.pairLeft e ∈ S ∨ Rxn.pairRight e ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs bad) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    · subst_vars; exact Or.inl hr
    · subst_vars; exact Or.inr hr

end AllIrrRAFCert.Hardness

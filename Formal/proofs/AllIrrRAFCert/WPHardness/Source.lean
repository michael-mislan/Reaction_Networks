import proofs.AllIrrRAFCert.Hardness.CliqueToRAF

namespace AllIrrRAFCert.WPHardness
open RAF RAF.Frankl

structure System (n q : Nat) where
  needs : Fin q → Finset (Fin (n+2))
  result : Fin q → Fin (n+2)

inductive Derives {n q : Nat} (A : System n q) (B : Finset (Fin (n+2))) : Fin (n+2) → Prop
  | seed {u} : u ∈ B → Derives A B u
  | rule (j : Fin q) : (∀ u ∈ A.needs j, Derives A B u) → Derives A B (A.result j)

def seeds {k n : Nat} (a : Fin k → Fin (n+2)) := Finset.univ.image a
def Generates {k n q : Nat} (A : System n q) (a : Fin k → Fin (n+2)) :=
  ∀ u, Derives A (seeds a) u

abbrev Vertex (k n : Nat) := Fin k × Fin (n+2)
inductive Mol (k n : Nat)
  | food
  | signal (v : Vertex k n)
  | guardCat (v : Vertex k n)
  | colorOK (i : Fin k)
  | statement (u : Fin (n+2))
  | globalCat
  deriving DecidableEq, Fintype
inductive Rxn (k n q : Nat)
  | selector (v : Vertex k n)
  | colorGate (v : Vertex k n)
  | rule (j : Fin q)
  | close
  deriving DecidableEq, Fintype
variable {k n q : Nat}
def next (v : Vertex k n) : Vertex k n :=
  (v.1,IrrRAFEnumeration.CircuitSource.nextAux v.2)
def crs (A : System n q) : CRS (Mol k n) (Rxn k n q) where
  food := {.food}
  inputs
    | .selector _ => {.food}
    | .colorGate v => (Finset.univ.erase v.2).image (fun w => .signal (v.1,w))
    | .rule j => insert .food ((A.needs j).image Mol.statement)
    | .close => Finset.univ.image Mol.colorOK ∪ Finset.univ.image Mol.statement
  outputs
    | .selector v => {.signal v,.guardCat v}
    | .colorGate v => {.colorOK v.1,.statement v.2}
    | .rule j => {.statement (A.result j)}
    | .close => {.globalCat}
def cat : Catalysis (Mol k n) (Rxn k n q)
  | .globalCat,_ => True
  | .guardCat u,.selector v => u = next v
  | _,_ => False
def guard (i : Fin k) : Finset (Rxn k n q) := Finset.univ.image (fun w => Rxn.selector (i,w))
@[simp] theorem selector_mem_guard (i : Fin k) (v : Vertex k n) :
    Rxn.selector v ∈ guard (q := q) i ↔ v.1=i := by simp [guard,Prod.ext_iff,eq_comm]
@[simp] theorem close_not_mem_guard (i : Fin k) : Rxn.close ∉ guard (n := n) (q := q) i := by simp [guard]

theorem signal_origin (A : System n q) (S : Finset (Rxn k n q)) {v : Vertex k n} {t : Nat}
    (h : Mol.signal v ∈ closureAt (crs A) S t) : Rxn.selector v ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    subst_vars; exact hr
theorem guardCat_origin (A : System n q) (S : Finset (Rxn k n q)) {v : Vertex k n} {t : Nat}
    (h : Mol.guardCat v ∈ closureAt (crs A) S t) : Rxn.selector v ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    subst_vars; exact hr
theorem globalCat_origin (A : System n q) (S : Finset (Rxn k n q)) {t : Nat}
    (h : Mol.globalCat ∈ closureAt (crs A) S t) : Rxn.close ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r <;> simp [crs] at ho
    exact hr
theorem colorOK_origin (A : System n q) (S : Finset (Rxn k n q)) {i : Fin k} {t : Nat}
    (h : Mol.colorOK i ∈ closureAt (crs A) S t) : ∃ w, Rxn.colorGate (i,w) ∈ S := by
  rcases mem_closureAt_imp_food_or_output (crs A) S h with hf | ⟨r,hr,ho⟩
  · simp [crs] at hf
  · cases r with
    | selector v => simp [crs] at ho
    | colorGate v =>
      simp [crs] at ho
      exact ⟨v.2,by simpa [ho] using hr⟩
    | rule j => simp [crs] at ho
    | close => simp [crs] at ho
end AllIrrRAFCert.WPHardness

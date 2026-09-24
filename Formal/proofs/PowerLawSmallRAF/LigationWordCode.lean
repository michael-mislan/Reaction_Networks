import proofs.PowerLawSmallRAF.FiniteLigationExposure
import proofs.RAF.Concrete.PolymerCRS

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete

/-- The source convention places the prefix in the most significant bits. -/
def ligationWordCode : LigationWord → Nat
  | [] => 0
  | b :: w => (if b then 2^w.length else 0) + ligationWordCode w

theorem ligationWordCode_lt (w : LigationWord) : ligationWordCode w < 2^w.length := by
  induction w with
  | nil => simp [ligationWordCode]
  | cons b w ih =>
    cases b <;> simp only [ligationWordCode, Bool.false_eq_true, ite_false, ite_true,
      zero_add, List.length_cons, pow_succ] <;> omega

theorem ligationWordCode_append (u v : LigationWord) :
    ligationWordCode (u ++ v) = ligationWordCode v + 2^v.length*ligationWordCode u := by
  induction u with
  | nil => simp [ligationWordCode]
  | cons b u ih =>
    cases b
    · simpa [ligationWordCode] using ih
    · simp only [List.cons_append, ligationWordCode, ite_true, List.length_append, pow_add, ih]
      ring

theorem ligationWordCode_injective_of_length {u v : LigationWord}
    (hlen : u.length = v.length) (hcode : ligationWordCode u = ligationWordCode v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v <;> simp_all
  | cons b u ih =>
    cases v with
    | nil => simp at hlen
    | cons c v =>
      have ht : u.length = v.length := by simpa using hlen
      have hu := ligationWordCode_lt u
      have hv := ligationWordCode_lt v
      cases b <;> cases c
      · have hc : ligationWordCode u = ligationWordCode v := by simpa [ligationWordCode] using hcode
        exact congrArg (List.cons false) (ih ht hc)
      · simp only [ligationWordCode, Bool.false_eq_true, ite_false, ite_true, zero_add] at hcode
        rw [ht] at hu
        omega
      · simp only [ligationWordCode, Bool.false_eq_true, ite_false, ite_true, zero_add] at hcode
        rw [ht] at hcode
        omega
      · have hc : ligationWordCode u = ligationWordCode v := by
          simp only [ligationWordCode, ite_true, ht] at hcode
          omega
        exact congrArg (List.cons true) (ih ht hc)

def ligationWordMolecule (n : Nat) (w : LigationWord) (h0 : 1 ≤ w.length) (hn : w.length ≤ n) :
    Molecule n := moleculeOfCode h0 hn ⟨ligationWordCode w, ligationWordCode_lt w⟩

@[simp] theorem ligationWordMolecule_length (n : Nat) (w : LigationWord)
    (h0 : 1 ≤ w.length) (hn : w.length ≤ n) :
    molLength (ligationWordMolecule n w h0 hn) = w.length :=
  molLength_moleculeOfCode h0 hn _

@[simp] theorem ligationWordMolecule_code (n : Nat) (w : LigationWord)
    (h0 : 1 ≤ w.length) (hn : w.length ≤ n) :
    (ligationWordMolecule n w h0 hn).2.val = ligationWordCode w := rfl

theorem ligationWordMolecule_injective (n : Nat) (u v : LigationWord)
    (hu0 : 1 ≤ u.length) (hun : u.length ≤ n)
    (hv0 : 1 ≤ v.length) (hvn : v.length ≤ n)
    (h : ligationWordMolecule n u hu0 hun = ligationWordMolecule n v hv0 hvn) : u = v := by
  apply ligationWordCode_injective_of_length
  · simpa using congrArg molLength h
  · simpa using congrArg (fun x : Molecule n => x.2.val) h

end PowerLawSmallRAF

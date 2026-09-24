import proofs.FutileCycle.AllNDeterminant
import proofs.FutileCycle.PositiveCore

namespace FutileCycle

def DeterminantClaim : Prop := ∀ (n : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (J : Child (futile n) I), J.matrix.det=0 ∨ J.matrix.det=1 ∨ J.matrix.det = -1

def AllPositiveClaim : Prop := ∀ (n : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (J : Child (futile n) I),
    MinimalUnstable (J.matrix.map (fun x : ℤ => (x:ℝ))) →
    J.matrix.det=(-1)^(Fintype.card I-1)

/-- A bound on the literal number of species of unstable-positive cores.
This is not a bound on templates modulo subdivision or contraction. -/
def BoundedPositiveClaim (B : ℕ) : Prop :=
  ∀ (n : ℕ) (I : Type) [Fintype I] [DecidableEq I] (J : Child (futile n) I),
    MinimalUnstable (J.matrix.map (fun x : ℤ => (x:ℝ))) →
    J.matrix.det=(-1)^(Fintype.card I-1) → Fintype.card I ≤ B

theorem not_all_positive : ¬AllPositiveClaim := by
  intro h
  obtain ⟨J,hd,hm⟩ := negative_core_all_n 3 (by omega)
  have hh := h 3 (Fin 6) J hm
  norm_num [hd] at hh

theorem positive_core_all_n (n : ℕ) (hn : 2 ≤ n) :
    ∃ J : Child (futile n) (PositiveIndex n),
      J.matrix.det=1 ∧ MinimalUnstable (J.matrix.map (fun x : ℤ => (x:ℝ))) ∧
      ∀ (s : Finset (PositiveIndex n)), s ≠ Finset.univ →
        DUnstableCores.DNonUnstable ((J.matrix.map (fun x : ℤ => (x:ℝ))).submatrix
          (fun i : s => i.val) (fun i : s => i.val)) := by
  refine ⟨positiveChild n hn,positive_det n hn,positive_minimal n hn,?_⟩
  intro s hs d hd
  exact positive_proper_scaling n hn s hs d hd

theorem no_literal_positive_bound (B : ℕ) : ¬BoundedPositiveClaim B := by
  intro h
  let n := B+2
  have hn : 2 ≤ n := by omega
  have hm := positive_minimal n hn
  have hd : (positiveChild n hn).matrix.det = (-1)^(Fintype.card (PositiveIndex n)-1) := by
    rw [positive_det, positive_dimension n hn]
    simp only [Nat.add_sub_cancel, pow_mul]
    norm_num
  have hh := h n (PositiveIndex n) (positiveChild n hn) hm hd
  rw [positive_dimension n hn] at hh
  omega

/-- The source-realized resolution: unit determinants, a negative core at all
n≥3, unbounded positive cores at all n≥2, and the two precise refutations. -/
theorem resolution :
    DeterminantClaim ∧
    (∀ n, 3 ≤ n → ∃ J : Child (futile n) (Fin 6), J.matrix.det=1 ∧
      MinimalUnstable (J.matrix.map (fun x : ℤ => (x:ℝ)))) ∧
    (∀ n, 2 ≤ n → ∃ J : Child (futile n) (PositiveIndex n), J.matrix.det=1 ∧
      MinimalUnstable (J.matrix.map (fun x : ℤ => (x:ℝ)))) ∧
    ¬AllPositiveClaim ∧ (∀ B, ¬BoundedPositiveClaim B) := by
  refine ⟨?_,negative_core_all_n,?_,not_all_positive,no_literal_positive_bound⟩
  · intro n I _ _ J
    exact allN_child_det n J
  · intro n hn
    obtain ⟨J,hd,hm,_⟩ := positive_core_all_n n hn
    exact ⟨J,hd,hm⟩

end FutileCycle

import proofs.FutileCycle.ReducedColumns
import proofs.FutileCycle.IntermediateElimination

namespace FutileCycle
open Matrix

theorem incidence_det_bound_fintype {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℤ) (h : SignedIncidence A) :
    A.det = 0 ∨ A.det = 1 ∨ A.det = -1 := by
  let e := (Fintype.equivFin I).symm
  have hh := incidence_det_bound (Fintype.card I) (A.submatrix e e)
    (h.submatrix e e e.injective)
  simpa [Matrix.det_submatrix_equiv_self] using hh

variable {S E C U V : Type*} [DecidableEq S] [DecidableEq E] [DecidableEq C]
    [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

def partitionedMatrix (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (v : V → C) (b : U → C) (d : V → Bool) : Matrix (U ⊕ V) (U ⊕ V) ℤ :=
  fun i j => stoich N
    (Sum.elim (fun i => freeEmbed (f i)) (fun k => .inr (.inr (v k))) i)
    (Sum.elim (fun j => (b j, .bind)) (fun k => (v k, outgoing (d k))) j)

theorem partitioned_det_bound (N : ConversionSystem S E C) (f : U → S ⊕ E)
    (hf : Function.Injective f) (v : V → C) (hv : Function.Injective v)
    (b : U → C) (d : V → Bool) :
    (partitionedMatrix N f v b d).det = 0 ∨
    (partitionedMatrix N f v b d).det = 1 ∨
    (partitionedMatrix N f v b d).det = -1 := by
  let B : Matrix U U ℤ := fun i j => stoich N (freeEmbed (f i)) (b j,.bind)
  let W : Matrix U V ℤ := fun i k => stoich N (freeEmbed (f i)) (v k,outgoing (d k))
  let K : Matrix V U ℤ := fun k j => if v k = b j then 1 else 0
  let T := B + W * K
  let D : Matrix U U ℤ := diagonal (fun i => rowSign (f i))
  let H : Matrix U U ℤ := fun i j => reducedColumn N f v d (b j) i
  have hH : H = D * T := by
    ext i j
    simp only [D, Matrix.diagonal_mul]
    rfl
  have hD : |D.det| = 1 := by
    simp only [D, det_diagonal, Finset.abs_prod]
    have hr : ∀ i, |rowSign (f i)| = 1 := by
      intro i
      cases f i <;> norm_num [rowSign]
    simp [hr]
  have hT : |H.det| = |T.det| := by
    rw [hH, det_mul, abs_mul, hD, one_mul]
  have hh := incidence_det_bound_fintype H
    (reducedColumns_signedIncidence N f hf v hv d b)
  have hTabs : |T.det| = 0 ∨ |T.det| = 1 := by
    rw [← hT]
    rcases hh with hh | hh | hh <;> simp only [hh] <;> norm_num
  have hA : partitionedMatrix N f v b d = fromBlocks B W K (-1) := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr k =>
      cases j with
      | inl j => simp [partitionedMatrix, fromBlocks, K, stoich, product, reactant]
      | inr l =>
        have hvl : v k = v l ↔ k = l := hv.eq_iff
        cases hdl : d l <;>
          simp [partitionedMatrix, fromBlocks, outgoing, hdl, stoich, product,
            reactant, Matrix.one_apply, hvl]
  have hAdet : (partitionedMatrix N f v b d).det =
      (-1) ^ Fintype.card V * T.det := by
    rw [hA, det_intermediate_elimination]
  have hAabs : |(partitionedMatrix N f v b d).det| = |T.det| := by
    rw [hAdet, abs_mul, abs_pow]
    norm_num
  rcases hTabs with ht | ht
  · left; exact abs_eq_zero.mp (hAabs.trans ht)
  · have := hAabs.trans ht
    right
    exact (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp this

end FutileCycle

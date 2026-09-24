import proofs.DUnstableCores.BlockTriangular

/-!
# Normalized one-articulation Hopf dichotomy

No branch inverse is used.  A zero articulation coordinate localizes the
imaginary eigenpair to the branch block.  Otherwise scalar normalization of
the eigenvector produces an exact complex branch solve, whose real and
imaginary parts are the campaign's inverse-free Schur message.
-/

namespace DUnstableCores

open scoped BigOperators

/-- Complex normalized branch equations before taking real and imaginary
parts. -/
structure ComplexHopfBranchWitness {ι : Type*} [Fintype ι]
    (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ) (omega : ℝ) where
  y : ι → ℂ
  branch : ∀ i,
    (c i : ℂ) + Matrix.mulVec (complexify B) y i =
      ((omega : ℂ) * Complex.I) * y i
  root : (a : ℂ) + ∑ j, (r j : ℂ) * y j =
    (omega : ℂ) * Complex.I

/-- Dividing a nonzero eigenvector by any nonzero scalar preserves the direct
matrix eigenpair equation. -/
theorem HasEigenpair.div_const
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {lam alpha : ℂ} {z : ι → ℂ}
    (h : HasEigenpair A lam z) (halpha : alpha ≠ 0) :
    HasEigenpair A lam (fun i => z i / alpha) := by
  constructor
  · intro hzero
    apply h.1
    funext i
    have hi := congrFun hzero i
    exact (div_eq_zero_iff.mp hi).resolve_right halpha
  · intro i
    calc
      Matrix.mulVec (complexify A) (fun j => z j / alpha) i =
          Matrix.mulVec (complexify A) z i / alpha := by
            simp [Matrix.mulVec, dotProduct, div_eq_mul_inv,
              Finset.sum_mul, mul_assoc]
      _ = (lam * z i) / alpha := by rw [h.2 i]
      _ = lam * (z i / alpha) := by ring

/-- The exact complex dichotomy at one articulation coordinate. -/
theorem imaginary_eigenpair_oneArticulation_complex_dichotomy
    {ι : Type*} [Fintype ι]
    (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ) (omega : ℝ)
    (z : Unit ⊕ ι → ℂ)
    (hpair : HasEigenpair (oneArticulationMatrix a r c B)
      ((omega : ℂ) * Complex.I) z) :
    (∃ y : ι → ℂ, HasEigenpair B ((omega : ℂ) * Complex.I) y) ∨
      Nonempty (ComplexHopfBranchWitness a r c B omega) := by
  classical
  by_cases hz0 : z (Sum.inl ()) = 0
  · left
    let y : ι → ℂ := fun i => z (Sum.inr i)
    have hyne : y ≠ 0 := by
      intro hy
      apply hpair.1
      funext x
      cases x with
      | inl u => simp [hz0]
      | inr i => exact congrFun hy i
    refine ⟨y, hyne, ?_⟩
    intro i
    have hi := hpair.2 (Sum.inr i)
    simp only [Matrix.mulVec, dotProduct] at hi
    rw [Fintype.sum_sum_type] at hi
    simpa [y, complexify, oneArticulationMatrix, hz0,
      Matrix.mulVec, dotProduct] using hi
  · right
    let zn : Unit ⊕ ι → ℂ := fun x => z x / z (Sum.inl ())
    have hnorm : HasEigenpair (oneArticulationMatrix a r c B)
        ((omega : ℂ) * Complex.I) zn := hpair.div_const hz0
    have hzn0 : zn (Sum.inl ()) = 1 := by
      simp [zn, hz0]
    let y : ι → ℂ := fun i => zn (Sum.inr i)
    constructor
    refine { y := y, branch := ?_, root := ?_ }
    · intro i
      have hi := hnorm.2 (Sum.inr i)
      simp only [Matrix.mulVec, dotProduct] at hi
      rw [Fintype.sum_sum_type] at hi
      simpa [y, complexify, oneArticulationMatrix, hzn0,
        Matrix.mulVec, dotProduct] using hi
    · have hroot := hnorm.2 (Sum.inl ())
      simp only [Matrix.mulVec, dotProduct] at hroot
      rw [Fintype.sum_sum_type] at hroot
      simpa [y, complexify, oneArticulationMatrix, hzn0] using hroot

/-- Taking real and imaginary parts of the normalized complex branch equations
recovers exactly the inverse-free two-real-coordinate Schur witness. -/
def ComplexHopfBranchWitness.toRealWitness
    {ι : Type*} [Fintype ι]
    {a omega : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : ComplexHopfBranchWitness a r c B omega) :
    HopfBranchSolveWitness a r c B omega := by
  let u : ι → ℝ := fun i => (w.y i).re
  let v : ι → ℝ := fun i => (w.y i).im
  refine { u := u
           v := v
           branch_real := ?_
           branch_imag := ?_
           root_real := ?_
           root_imag := ?_ }
  · intro i
    change -B.mulVec (fun j => (w.y j).re) i - omega * (w.y i).im = c i
    have h := congrArg Complex.re (w.branch i)
    simp [Matrix.mulVec, dotProduct, complexify] at h
    simp only [Matrix.mulVec, dotProduct]
    linarith
  · intro i
    change omega * (w.y i).re - B.mulVec (fun j => (w.y j).im) i = 0
    have h := congrArg Complex.im (w.branch i)
    simp [Matrix.mulVec, dotProduct, complexify] at h
    simp only [Matrix.mulVec, dotProduct]
    linarith
  · have h := congrArg Complex.re w.root
    simp at h
    simpa [dotProduct, u] using h
  · have h := congrArg Complex.im w.root
    simp at h
    simpa [dotProduct, v] using h

/-- Public inverse-free one-articulation theorem: imaginary phase either lives
entirely in the branch block or yields the exact Schur message. -/
theorem imaginary_eigenpair_oneArticulation_dichotomy
    {ι : Type*} [Fintype ι]
    (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ) (omega : ℝ)
    (z : Unit ⊕ ι → ℂ)
    (hpair : HasEigenpair (oneArticulationMatrix a r c B)
      ((omega : ℂ) * Complex.I) z) :
    (∃ y : ι → ℂ, HasEigenpair B ((omega : ℂ) * Complex.I) y) ∨
      Nonempty (HopfBranchSolveWitness a r c B omega) := by
  cases imaginary_eigenpair_oneArticulation_complex_dichotomy
      a r c B omega z hpair with
  | inl hlocal => exact Or.inl hlocal
  | inr hw =>
      obtain ⟨w⟩ := hw
      exact Or.inr ⟨w.toRealWitness⟩

end DUnstableCores

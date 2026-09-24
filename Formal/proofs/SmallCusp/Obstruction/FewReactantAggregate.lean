import proofs.SmallCusp.Obstruction.CubicDegeneracy
import proofs.SmallCusp.Source.Enumeration


namespace SmallCusp

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

def aggregateMass (w : BimolComplexCode → Species → ℝ) (i : Species) : ℝ :=
  w .zero i + w .x i + w .y i + w .xx i + w .xy i + w .yy i

def aggregateJacobian (w : BimolComplexCode → Species → ℝ)
    (i j : Species) : ℝ :=
  w .zero i * ((BimolComplexCode.decode .zero j : ℕ) : ℝ) +
  w .x i * ((BimolComplexCode.decode .x j : ℕ) : ℝ) +
  w .y i * ((BimolComplexCode.decode .y j : ℕ) : ℝ) +
  w .xx i * ((BimolComplexCode.decode .xx j : ℕ) : ℝ) +
  w .xy i * ((BimolComplexCode.decode .xy j : ℕ) : ℝ) +
  w .yy i * ((BimolComplexCode.decode .yy j : ℕ) : ℝ)

def aggregateDet (w : BimolComplexCode → Species → ℝ) : ℝ :=
  aggregateJacobian w 0 0 * aggregateJacobian w 1 1 -
    aggregateJacobian w 0 1 * aggregateJacobian w 1 0

def aggregateRightKernel (w : BimolComplexCode → Species → ℝ)
    (alternate : Bool) : Species → ℝ :=
  if alternate then ![aggregateJacobian w 1 1, -aggregateJacobian w 1 0]
  else ![-aggregateJacobian w 0 1, aggregateJacobian w 0 0]

def aggregateLeftKernel (w : BimolComplexCode → Species → ℝ)
    (alternate : Bool) : Species → ℝ :=
  if alternate then ![aggregateJacobian w 1 1, -aggregateJacobian w 0 1]
  else ![-aggregateJacobian w 1 0, aggregateJacobian w 0 0]

def aggregateHessianScalar (c : BimolComplexCode)
    (q h : Species → ℝ) : ℝ :=
  let x := (BimolComplexCode.decode c 0 : ℝ)
  let y := (BimolComplexCode.decode c 1 : ℝ)
  x * (x - 1) * q 0 * h 0 + x * y * (q 0 * h 1 + q 1 * h 0) +
    y * (y - 1) * q 1 * h 1

def aggregateHessianApply (w : BimolComplexCode → Species → ℝ)
    (q h : Species → ℝ) (i : Species) : ℝ :=
  w .zero i * aggregateHessianScalar .zero q h +
  w .x i * aggregateHessianScalar .x q h +
  w .y i * aggregateHessianScalar .y q h +
  w .xx i * aggregateHessianScalar .xx q h +
  w .xy i * aggregateHessianScalar .xy q h +
  w .yy i * aggregateHessianScalar .yy q h

def aggregateMixed (w : BimolComplexCode → Species → ℝ)
    (rightAlternate leftAlternate : Bool) (h : Species → ℝ) : ℝ :=
  dot (aggregateLeftKernel w leftAlternate)
    (aggregateHessianApply w (aggregateRightKernel w rightAlternate) h)
theorem fewReactant_000_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .zero 0 = -(0) := by linarith
  have hlast1 : w .zero 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_000_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .zero 0 = -(0) := by linarith
  have hlast1 : w .zero 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_000_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .zero 0 = -(0) := by linarith
  have hlast1 : w .zero 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_000_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .zero 0 = -(0) := by linarith
  have hlast1 : w .zero 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_001_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(0) := by linarith
  have hlast1 : w .x 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_001_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(0) := by linarith
  have hlast1 : w .x 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_001_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(0) := by linarith
  have hlast1 : w .x 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_001_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(0) := by linarith
  have hlast1 : w .x 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_002_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(0) := by linarith
  have hlast1 : w .y 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_002_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(0) := by linarith
  have hlast1 : w .y 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_002_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(0) := by linarith
  have hlast1 : w .y 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_002_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(0) := by linarith
  have hlast1 : w .y 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_003_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(0) := by linarith
  have hlast1 : w .xx 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_003_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(0) := by linarith
  have hlast1 : w .xx 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_003_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(0) := by linarith
  have hlast1 : w .xx 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_003_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(0) := by linarith
  have hlast1 : w .xx 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_004_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(0) := by linarith
  have hlast1 : w .xy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_004_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(0) := by linarith
  have hlast1 : w .xy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_004_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(0) := by linarith
  have hlast1 : w .xy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_004_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(0) := by linarith
  have hlast1 : w .xy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_005_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(0) := by linarith
  have hlast1 : w .yy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_005_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(0) := by linarith
  have hlast1 : w .yy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_005_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(0) := by linarith
  have hlast1 : w .yy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_005_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(0) := by linarith
  have hlast1 : w .yy 1 = -(0) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_006_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(w .zero 0) := by linarith
  have hlast1 : w .x 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_006_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(w .zero 0) := by linarith
  have hlast1 : w .x 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_006_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(w .zero 0) := by linarith
  have hlast1 : w .x 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_006_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .x 0 = -(w .zero 0) := by linarith
  have hlast1 : w .x 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_007_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_007_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_007_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_007_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_008_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_008_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_008_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_008_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_009_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_009_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_009_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_009_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_010_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_010_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_010_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_010_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_011_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_011_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_011_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_011_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_012_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_012_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_012_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_012_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_013_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_013_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_013_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_013_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_014_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_014_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_014_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_014_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_015_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_015_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_015_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_015_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_016_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_016_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_016_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_016_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_017_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_017_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_017_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_017_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_018_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_018_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_018_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_018_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_019_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_019_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_019_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_019_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_020_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hlast0, hlast1] <;> ring

theorem fewReactant_020_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hlast0, hlast1] <;> ring

theorem fewReactant_020_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hlast0, hlast1] <;> ring

theorem fewReactant_020_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hz3, hlast0, hlast1] <;> ring

theorem fewReactant_021_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_021_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_021_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_021_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .y} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz3, hz4, hz5] at heq0 heq1
  have hlast0 : w .y 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .y 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz3, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_022_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_022_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_022_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_022_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_023_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz2, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .zero 0 + h 1 * w .x 0 + (-1 : ℝ) * h 0 * w .zero 0) * hdet

theorem fewReactant_023_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_023_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz2, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .zero 1 + (-1 : ℝ) * h 1 * w .zero 1 + (-1 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_023_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz2, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_024_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz2, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .x 0) * hdet

theorem fewReactant_024_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_024_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz2, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_024_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .x, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz2, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .x 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .x 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz2, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_025_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_025_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_025_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz4, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_025_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .y 1) * hdet

theorem fewReactant_026_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_026_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .zero 0 + (-1 : ℝ) * h 0 * w .zero 0 + (-1 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_026_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz5, hlast0, hlast1] <;> ring

theorem fewReactant_026_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .zero 1 + h 0 * w .y 1 + (-1 : ℝ) * h 1 * w .zero 1) * hdet

theorem fewReactant_027_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_027_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_027_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_027_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz1, hz3, hz4, hlast0, hlast1] <;> ring

theorem fewReactant_028_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .zero 0 + h 1 * w .xx 0 + (-2 : ℝ) * h 0 * w .zero 0) * hdet

theorem fewReactant_028_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .zero 0 + h 0 * w .xx 0) * hdet

theorem fewReactant_028_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 1 * w .zero 1 + (-1 : ℝ) * h 1 * w .xx 1 + (2 : ℝ) * h 0 * w .zero 1) * hdet

theorem fewReactant_028_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz1, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .zero 1 + (-1 : ℝ) * h 0 * w .xx 1) * hdet

theorem fewReactant_029_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 1 * w .xx 0) * hdet

theorem fewReactant_029_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 0 * w .zero 0 + (2 : ℝ) * h 0 * w .xx 0) * hdet

theorem fewReactant_029_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_029_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz1, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .zero 1 + (-2 : ℝ) * h 0 * w .xx 1) * hdet

theorem fewReactant_030_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .xy 0) * hdet

theorem fewReactant_030_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .xy 0 + (2 : ℝ) * h 1 * w .zero 0) * hdet

theorem fewReactant_030_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 1 * w .xy 1) * hdet

theorem fewReactant_030_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.zero, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz1, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .zero 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .zero 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz1, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .xy 1 + (-2 : ℝ) * h 1 * w .zero 1) * hdet

theorem fewReactant_031_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_031_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_031_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 0 * w .y 1) * hdet

theorem fewReactant_031_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xx} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz4 := hsupport .xy (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz4, hz5] at heq0 heq1
  have hlast0 : w .xx 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xx 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz4, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 0 * w .y 1) * hdet

theorem fewReactant_032_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .x 0 + (-1 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_032_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .x 0 + (-1 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_032_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .y 1 + (-1 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_032_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz3, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .y 1 + (-1 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_033_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 1 * w .x 0) * hdet

theorem fewReactant_033_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 1 * w .x 0) * hdet

theorem fewReactant_033_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_033_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .y, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz3 := hsupport .xx (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz3, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .y 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .y 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz3, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_034_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .xx 0 + h 1 * w .x 0 + h 1 * w .xx 0) * hdet

theorem fewReactant_034_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 0 * w .x 0 + (2 : ℝ) * h 0 * w .xx 0) * hdet

theorem fewReactant_034_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .xx 1 + (-1 : ℝ) * h 1 * w .x 1 + (-1 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_034_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz2, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .x 1 + (-2 : ℝ) * h 0 * w .xx 1) * hdet

theorem fewReactant_035_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 1 * w .x 0 + (2 : ℝ) * h 0 * w .x 0 + (2 : ℝ) * h 0 * w .xx 0 + (2 : ℝ) * h 1 * w .xx 0) * hdet

theorem fewReactant_035_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((4 : ℝ) * h 0 * w .x 0 + (4 : ℝ) * h 0 * w .xx 0) * hdet

theorem fewReactant_035_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 1 * w .x 1 + (-2 : ℝ) * h 0 * w .x 1 + (-2 : ℝ) * h 0 * w .xx 1 + (-2 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_035_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz2, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-4 : ℝ) * h 0 * w .x 1 + (-4 : ℝ) * h 0 * w .xx 1) * hdet

theorem fewReactant_036_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .x 0 + h 0 * w .xy 0 + h 1 * w .xy 0 + (2 : ℝ) * h 1 * w .x 0) * hdet

theorem fewReactant_036_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 0 * w .x 0 + (2 : ℝ) * h 0 * w .xy 0 + (2 : ℝ) * h 1 * w .x 0) * hdet

theorem fewReactant_036_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .x 1 + (-1 : ℝ) * h 0 * w .xy 1 + (-1 : ℝ) * h 1 * w .xy 1 + (-2 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_036_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.x, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz2 := hsupport .y (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz2, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .x 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .x 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz2, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .x 1 + (-2 : ℝ) * h 0 * w .xy 1 + (-2 : ℝ) * h 1 * w .x 1) * hdet

theorem fewReactant_037_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 0 * w .y 0 + (2 : ℝ) * h 1 * w .xx 0) * hdet

theorem fewReactant_037_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .xx 0 + h 1 * w .xx 0 + (-1 : ℝ) * h 0 * w .y 0) * hdet

theorem fewReactant_037_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 1 * w .xx 1 + (2 : ℝ) * h 0 * w .y 1) * hdet

theorem fewReactant_037_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .xy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz5 := hsupport .yy (by decide)
  simp [aggregateMass, hz0, hz1, hz5] at heq0 heq1
  have hlast0 : w .xy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .xy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz5, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .y 1 + (-1 : ℝ) * h 0 * w .xx 1 + (-1 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_038_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((4 : ℝ) * h 1 * w .xx 0) * hdet

theorem fewReactant_038_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .y 0 + (2 : ℝ) * h 0 * w .xx 0 + (2 : ℝ) * h 1 * w .xx 0) * hdet

theorem fewReactant_038_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-4 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_038_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xx, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz4 := hsupport .xy (by decide)
  simp [aggregateMass, hz0, hz1, hz4] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xx 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xx 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz4, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .y 1 + (-2 : ℝ) * h 0 * w .xx 1 + (-2 : ℝ) * h 1 * w .xx 1) * hdet

theorem fewReactant_039_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((2 : ℝ) * h 1 * w .xy 0) * hdet

theorem fewReactant_039_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination (h 0 * w .xy 0 + h 1 * w .y 0 + h 1 * w .xy 0) * hdet

theorem fewReactant_039_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-2 : ℝ) * h 1 * w .xy 1) * hdet

theorem fewReactant_039_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.y, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz3 := hsupport .xx (by decide)
  simp [aggregateMass, hz0, hz1, hz3] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .y 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .y 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode, aggregateDet,
    aggregateRightKernel,
    aggregateLeftKernel, aggregateHessianApply, aggregateHessianScalar,
    aggregateMixed, dot, hz0, hz1, hz3, hlast0, hlast1] at hdet ⊢
  all_goals
    ring_nf at hdet ⊢
    linear_combination ((-1 : ℝ) * h 0 * w .xy 1 + (-1 : ℝ) * h 1 * w .y 1 + (-1 : ℝ) * h 1 * w .xy 1) * hdet

theorem fewReactant_040_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  simp [aggregateMass, hz0, hz1, hz2] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hlast0, hlast1] <;> ring

theorem fewReactant_040_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  simp [aggregateMass, hz0, hz1, hz2] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hlast0, hlast1] <;> ring

theorem fewReactant_040_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  simp [aggregateMass, hz0, hz1, hz2] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hlast0, hlast1] <;> ring

theorem fewReactant_040_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ)
    (hsupport : ∀ c, c ∉ ({.xx, .xy, .yy} : Finset BimolComplexCode) → w c = 0)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (_hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  have hz0 := hsupport .zero (by decide)
  have hz1 := hsupport .x (by decide)
  have hz2 := hsupport .y (by decide)
  simp [aggregateMass, hz0, hz1, hz2] at heq0 heq1
  have hlast0 : w .yy 0 = -(w .xx 0 + w .xy 0) := by linarith
  have hlast1 : w .yy 1 = -(w .xx 1 + w .xy 1) := by linarith
  simp [aggregateJacobian, BimolComplexCode.decode,
    aggregateRightKernel, aggregateLeftKernel,
    aggregateHessianApply, aggregateHessianScalar, aggregateMixed, dot,
    hz0, hz1, hz2, hlast0, hlast1] <;> ring

def FewReactantAggregateSupport (w : BimolComplexCode → Species → ℝ) : Prop :=
  (∀ c, c ∉ ({.zero} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .x} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .y} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .y} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xx, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xx, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xy, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .x, .y} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .x, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .x, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .x, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .y, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .y, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .y, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .xx, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .xx, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.zero, .xy, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .y, .xx} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .y, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .y, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .xx, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .xx, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.x, .xy, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .xx, .xy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .xx, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.y, .xy, .yy} : Finset BimolComplexCode) → w c = 0) ∨
  (∀ c, c ∉ ({.xx, .xy, .yy} : Finset BimolComplexCode) → w c = 0)

theorem bimolSupport_card_le_three_cover :
    ∀ S : Finset BimolComplexCode, S.card ≤ 3 →
      S ⊆ ({.zero} : Finset BimolComplexCode) ∨
      S ⊆ ({.x} : Finset BimolComplexCode) ∨
      S ⊆ ({.y} : Finset BimolComplexCode) ∨
      S ⊆ ({.xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .x} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .y} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .y} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.xx, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.xx, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.xy, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .x, .y} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .x, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .x, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .x, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .y, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .y, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .y, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .xx, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .xx, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.zero, .xy, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .y, .xx} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .y, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .y, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .xx, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .xx, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.x, .xy, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .xx, .xy} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .xx, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.y, .xy, .yy} : Finset BimolComplexCode) ∨
      S ⊆ ({.xx, .xy, .yy} : Finset BimolComplexCode) := by
  native_decide

theorem fewReactantAggregateSupport_of_card_le_three
    (w : BimolComplexCode → Species → ℝ)
    (S : Finset BimolComplexCode) (hcard : S.card ≤ 3)
    (hzero : ∀ c, c ∉ S → w c = 0) :
    FewReactantAggregateSupport w := by
  have hcover := bimolSupport_card_le_three_cover S hcard
  rcases hcover with hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub | hsub
  ·
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    left
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))
  ·
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    right
    intro c hc
    exact hzero c (fun hcS => hc (hsub hcS))

theorem fewReactantAggregate_00 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ) (hsupport : FewReactantAggregateSupport w)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false false h = 0 := by
  rcases hsupport with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact fewReactant_000_00 w h hs heq0 heq1 hdet
  · exact fewReactant_001_00 w h hs heq0 heq1 hdet
  · exact fewReactant_002_00 w h hs heq0 heq1 hdet
  · exact fewReactant_003_00 w h hs heq0 heq1 hdet
  · exact fewReactant_004_00 w h hs heq0 heq1 hdet
  · exact fewReactant_005_00 w h hs heq0 heq1 hdet
  · exact fewReactant_006_00 w h hs heq0 heq1 hdet
  · exact fewReactant_007_00 w h hs heq0 heq1 hdet
  · exact fewReactant_008_00 w h hs heq0 heq1 hdet
  · exact fewReactant_009_00 w h hs heq0 heq1 hdet
  · exact fewReactant_010_00 w h hs heq0 heq1 hdet
  · exact fewReactant_011_00 w h hs heq0 heq1 hdet
  · exact fewReactant_012_00 w h hs heq0 heq1 hdet
  · exact fewReactant_013_00 w h hs heq0 heq1 hdet
  · exact fewReactant_014_00 w h hs heq0 heq1 hdet
  · exact fewReactant_015_00 w h hs heq0 heq1 hdet
  · exact fewReactant_016_00 w h hs heq0 heq1 hdet
  · exact fewReactant_017_00 w h hs heq0 heq1 hdet
  · exact fewReactant_018_00 w h hs heq0 heq1 hdet
  · exact fewReactant_019_00 w h hs heq0 heq1 hdet
  · exact fewReactant_020_00 w h hs heq0 heq1 hdet
  · exact fewReactant_021_00 w h hs heq0 heq1 hdet
  · exact fewReactant_022_00 w h hs heq0 heq1 hdet
  · exact fewReactant_023_00 w h hs heq0 heq1 hdet
  · exact fewReactant_024_00 w h hs heq0 heq1 hdet
  · exact fewReactant_025_00 w h hs heq0 heq1 hdet
  · exact fewReactant_026_00 w h hs heq0 heq1 hdet
  · exact fewReactant_027_00 w h hs heq0 heq1 hdet
  · exact fewReactant_028_00 w h hs heq0 heq1 hdet
  · exact fewReactant_029_00 w h hs heq0 heq1 hdet
  · exact fewReactant_030_00 w h hs heq0 heq1 hdet
  · exact fewReactant_031_00 w h hs heq0 heq1 hdet
  · exact fewReactant_032_00 w h hs heq0 heq1 hdet
  · exact fewReactant_033_00 w h hs heq0 heq1 hdet
  · exact fewReactant_034_00 w h hs heq0 heq1 hdet
  · exact fewReactant_035_00 w h hs heq0 heq1 hdet
  · exact fewReactant_036_00 w h hs heq0 heq1 hdet
  · exact fewReactant_037_00 w h hs heq0 heq1 hdet
  · exact fewReactant_038_00 w h hs heq0 heq1 hdet
  · exact fewReactant_039_00 w h hs heq0 heq1 hdet
  · exact fewReactant_040_00 w h hs heq0 heq1 hdet

theorem fewReactantAggregate_01 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ) (hsupport : FewReactantAggregateSupport w)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w false true h = 0 := by
  rcases hsupport with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact fewReactant_000_01 w h hs heq0 heq1 hdet
  · exact fewReactant_001_01 w h hs heq0 heq1 hdet
  · exact fewReactant_002_01 w h hs heq0 heq1 hdet
  · exact fewReactant_003_01 w h hs heq0 heq1 hdet
  · exact fewReactant_004_01 w h hs heq0 heq1 hdet
  · exact fewReactant_005_01 w h hs heq0 heq1 hdet
  · exact fewReactant_006_01 w h hs heq0 heq1 hdet
  · exact fewReactant_007_01 w h hs heq0 heq1 hdet
  · exact fewReactant_008_01 w h hs heq0 heq1 hdet
  · exact fewReactant_009_01 w h hs heq0 heq1 hdet
  · exact fewReactant_010_01 w h hs heq0 heq1 hdet
  · exact fewReactant_011_01 w h hs heq0 heq1 hdet
  · exact fewReactant_012_01 w h hs heq0 heq1 hdet
  · exact fewReactant_013_01 w h hs heq0 heq1 hdet
  · exact fewReactant_014_01 w h hs heq0 heq1 hdet
  · exact fewReactant_015_01 w h hs heq0 heq1 hdet
  · exact fewReactant_016_01 w h hs heq0 heq1 hdet
  · exact fewReactant_017_01 w h hs heq0 heq1 hdet
  · exact fewReactant_018_01 w h hs heq0 heq1 hdet
  · exact fewReactant_019_01 w h hs heq0 heq1 hdet
  · exact fewReactant_020_01 w h hs heq0 heq1 hdet
  · exact fewReactant_021_01 w h hs heq0 heq1 hdet
  · exact fewReactant_022_01 w h hs heq0 heq1 hdet
  · exact fewReactant_023_01 w h hs heq0 heq1 hdet
  · exact fewReactant_024_01 w h hs heq0 heq1 hdet
  · exact fewReactant_025_01 w h hs heq0 heq1 hdet
  · exact fewReactant_026_01 w h hs heq0 heq1 hdet
  · exact fewReactant_027_01 w h hs heq0 heq1 hdet
  · exact fewReactant_028_01 w h hs heq0 heq1 hdet
  · exact fewReactant_029_01 w h hs heq0 heq1 hdet
  · exact fewReactant_030_01 w h hs heq0 heq1 hdet
  · exact fewReactant_031_01 w h hs heq0 heq1 hdet
  · exact fewReactant_032_01 w h hs heq0 heq1 hdet
  · exact fewReactant_033_01 w h hs heq0 heq1 hdet
  · exact fewReactant_034_01 w h hs heq0 heq1 hdet
  · exact fewReactant_035_01 w h hs heq0 heq1 hdet
  · exact fewReactant_036_01 w h hs heq0 heq1 hdet
  · exact fewReactant_037_01 w h hs heq0 heq1 hdet
  · exact fewReactant_038_01 w h hs heq0 heq1 hdet
  · exact fewReactant_039_01 w h hs heq0 heq1 hdet
  · exact fewReactant_040_01 w h hs heq0 heq1 hdet

theorem fewReactantAggregate_10 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ) (hsupport : FewReactantAggregateSupport w)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true false h = 0 := by
  rcases hsupport with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact fewReactant_000_10 w h hs heq0 heq1 hdet
  · exact fewReactant_001_10 w h hs heq0 heq1 hdet
  · exact fewReactant_002_10 w h hs heq0 heq1 hdet
  · exact fewReactant_003_10 w h hs heq0 heq1 hdet
  · exact fewReactant_004_10 w h hs heq0 heq1 hdet
  · exact fewReactant_005_10 w h hs heq0 heq1 hdet
  · exact fewReactant_006_10 w h hs heq0 heq1 hdet
  · exact fewReactant_007_10 w h hs heq0 heq1 hdet
  · exact fewReactant_008_10 w h hs heq0 heq1 hdet
  · exact fewReactant_009_10 w h hs heq0 heq1 hdet
  · exact fewReactant_010_10 w h hs heq0 heq1 hdet
  · exact fewReactant_011_10 w h hs heq0 heq1 hdet
  · exact fewReactant_012_10 w h hs heq0 heq1 hdet
  · exact fewReactant_013_10 w h hs heq0 heq1 hdet
  · exact fewReactant_014_10 w h hs heq0 heq1 hdet
  · exact fewReactant_015_10 w h hs heq0 heq1 hdet
  · exact fewReactant_016_10 w h hs heq0 heq1 hdet
  · exact fewReactant_017_10 w h hs heq0 heq1 hdet
  · exact fewReactant_018_10 w h hs heq0 heq1 hdet
  · exact fewReactant_019_10 w h hs heq0 heq1 hdet
  · exact fewReactant_020_10 w h hs heq0 heq1 hdet
  · exact fewReactant_021_10 w h hs heq0 heq1 hdet
  · exact fewReactant_022_10 w h hs heq0 heq1 hdet
  · exact fewReactant_023_10 w h hs heq0 heq1 hdet
  · exact fewReactant_024_10 w h hs heq0 heq1 hdet
  · exact fewReactant_025_10 w h hs heq0 heq1 hdet
  · exact fewReactant_026_10 w h hs heq0 heq1 hdet
  · exact fewReactant_027_10 w h hs heq0 heq1 hdet
  · exact fewReactant_028_10 w h hs heq0 heq1 hdet
  · exact fewReactant_029_10 w h hs heq0 heq1 hdet
  · exact fewReactant_030_10 w h hs heq0 heq1 hdet
  · exact fewReactant_031_10 w h hs heq0 heq1 hdet
  · exact fewReactant_032_10 w h hs heq0 heq1 hdet
  · exact fewReactant_033_10 w h hs heq0 heq1 hdet
  · exact fewReactant_034_10 w h hs heq0 heq1 hdet
  · exact fewReactant_035_10 w h hs heq0 heq1 hdet
  · exact fewReactant_036_10 w h hs heq0 heq1 hdet
  · exact fewReactant_037_10 w h hs heq0 heq1 hdet
  · exact fewReactant_038_10 w h hs heq0 heq1 hdet
  · exact fewReactant_039_10 w h hs heq0 heq1 hdet
  · exact fewReactant_040_10 w h hs heq0 heq1 hdet

theorem fewReactantAggregate_11 (w : BimolComplexCode → Species → ℝ)
    (h : Species → ℝ) (hsupport : FewReactantAggregateSupport w)
    (heq0 : aggregateMass w 0 = 0) (heq1 : aggregateMass w 1 = 0)
    (hdet : aggregateDet w = 0) :
    aggregateMixed w true true h = 0 := by
  rcases hsupport with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs | hs
  · exact fewReactant_000_11 w h hs heq0 heq1 hdet
  · exact fewReactant_001_11 w h hs heq0 heq1 hdet
  · exact fewReactant_002_11 w h hs heq0 heq1 hdet
  · exact fewReactant_003_11 w h hs heq0 heq1 hdet
  · exact fewReactant_004_11 w h hs heq0 heq1 hdet
  · exact fewReactant_005_11 w h hs heq0 heq1 hdet
  · exact fewReactant_006_11 w h hs heq0 heq1 hdet
  · exact fewReactant_007_11 w h hs heq0 heq1 hdet
  · exact fewReactant_008_11 w h hs heq0 heq1 hdet
  · exact fewReactant_009_11 w h hs heq0 heq1 hdet
  · exact fewReactant_010_11 w h hs heq0 heq1 hdet
  · exact fewReactant_011_11 w h hs heq0 heq1 hdet
  · exact fewReactant_012_11 w h hs heq0 heq1 hdet
  · exact fewReactant_013_11 w h hs heq0 heq1 hdet
  · exact fewReactant_014_11 w h hs heq0 heq1 hdet
  · exact fewReactant_015_11 w h hs heq0 heq1 hdet
  · exact fewReactant_016_11 w h hs heq0 heq1 hdet
  · exact fewReactant_017_11 w h hs heq0 heq1 hdet
  · exact fewReactant_018_11 w h hs heq0 heq1 hdet
  · exact fewReactant_019_11 w h hs heq0 heq1 hdet
  · exact fewReactant_020_11 w h hs heq0 heq1 hdet
  · exact fewReactant_021_11 w h hs heq0 heq1 hdet
  · exact fewReactant_022_11 w h hs heq0 heq1 hdet
  · exact fewReactant_023_11 w h hs heq0 heq1 hdet
  · exact fewReactant_024_11 w h hs heq0 heq1 hdet
  · exact fewReactant_025_11 w h hs heq0 heq1 hdet
  · exact fewReactant_026_11 w h hs heq0 heq1 hdet
  · exact fewReactant_027_11 w h hs heq0 heq1 hdet
  · exact fewReactant_028_11 w h hs heq0 heq1 hdet
  · exact fewReactant_029_11 w h hs heq0 heq1 hdet
  · exact fewReactant_030_11 w h hs heq0 heq1 hdet
  · exact fewReactant_031_11 w h hs heq0 heq1 hdet
  · exact fewReactant_032_11 w h hs heq0 heq1 hdet
  · exact fewReactant_033_11 w h hs heq0 heq1 hdet
  · exact fewReactant_034_11 w h hs heq0 heq1 hdet
  · exact fewReactant_035_11 w h hs heq0 heq1 hdet
  · exact fewReactant_036_11 w h hs heq0 heq1 hdet
  · exact fewReactant_037_11 w h hs heq0 heq1 hdet
  · exact fewReactant_038_11 w h hs heq0 heq1 hdet
  · exact fewReactant_039_11 w h hs heq0 heq1 hdet
  · exact fewReactant_040_11 w h hs heq0 heq1 hdet


end SmallCusp

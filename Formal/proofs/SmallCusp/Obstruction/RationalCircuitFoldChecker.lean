import proofs.SmallCusp.Obstruction.RationalCircuitFold

/-!
# Computable reflected checker for rational circuit-fold identities

Homogeneous quadratic and quartic polynomials are represented by dense
coefficient tensors.  Symmetrization preserves evaluation and turns each
commutative monomial coefficient into an executable pointwise coefficient.
-/

open scoped BigOperators

namespace SmallCusp

def rationalQuadraticEval {R : Type*} [Field R] {g : ℕ}
    (coeff : Fin g → Fin g → R) (t : Fin g → R) : R :=
  ∑ a, ∑ b, coeff a b * t a * t b

def rationalQuarticEval {R : Type*} [Field R] {g : ℕ}
    (coeff : Fin g → Fin g → Fin g → Fin g → R)
    (t : Fin g → R) : R :=
  ∑ a, ∑ b, ∑ c, ∑ d, coeff a b c d * t a * t b * t c * t d

def symmetrizeQuadratic {R : Type*} [Field R] {g : ℕ}
    (coeff : Fin g → Fin g → R) : Fin g → Fin g → R :=
  fun a b ↦ (coeff a b + coeff b a) / 2

def symmetrizeQuartic {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) :
    Fin g → Fin g → Fin g → Fin g → R :=
  fun a b c d ↦ (
    f a b c d + f a b d c + f a c b d + f a c d b + f a d b c + f a d c b +
    f b a c d + f b a d c + f b c a d + f b c d a + f b d a c + f b d c a +
    f c a b d + f c a d b + f c b a d + f c b d a + f c d a b + f c d b a +
    f d a b c + f d a c b + f d b a c + f d b c a + f d c a b + f d c b a) / 24

theorem rationalQuadraticEval_swap
    {R : Type*} [Field R] {g : ℕ} (f : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (fun a b ↦ f b a) t =
      rationalQuadraticEval f t := by
  simp only [rationalQuadraticEval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rationalQuadraticEval_add {R : Type*} [Field R] {g : ℕ}
    (f h : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (fun a b ↦ f a b + h a b) t =
      rationalQuadraticEval f t + rationalQuadraticEval h t := by
  simp [rationalQuadraticEval, add_mul, Finset.sum_add_distrib]

theorem rationalQuadraticEval_sub {R : Type*} [Field R] {g : ℕ}
    (f h : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (fun a b ↦ f a b - h a b) t =
      rationalQuadraticEval f t - rationalQuadraticEval h t := by
  simp [rationalQuadraticEval, sub_mul, Finset.sum_sub_distrib]

theorem rationalQuadraticEval_smul {R : Type*} [Field R] {g : ℕ} (q : R)
    (f : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (fun a b ↦ q * f a b) t =
      q * rationalQuadraticEval f t := by
  simp only [rationalQuadraticEval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rationalQuadraticEval_symmetrize
    {R : Type*} [Field R] [CharZero R] {g : ℕ}
    (f : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (symmetrizeQuadratic f) t =
      rationalQuadraticEval f t := by
  rw [show symmetrizeQuadratic f =
      fun a b ↦ (1 / 2 : R) * (f a b + f b a) by
    funext a b
    simp [symmetrizeQuadratic]
    ring]
  rw [rationalQuadraticEval_smul, rationalQuadraticEval_add,
    rationalQuadraticEval_swap]
  ring

theorem rationalQuarticEval_swap01
    {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f b a c d) t =
      rationalQuarticEval f t := by
  simp only [rationalQuarticEval]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem rationalQuarticEval_swap12
    {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f a c b d) t =
      rationalQuarticEval f t := by
  simp only [rationalQuarticEval]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem rationalQuarticEval_swap23
    {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f a b d c) t =
      rationalQuarticEval f t := by
  simp only [rationalQuarticEval]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem rationalQuarticEval_add {R : Type*} [Field R] {g : ℕ}
    (f h : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f a b c d + h a b c d) t =
      rationalQuarticEval f t + rationalQuarticEval h t := by
  simp [rationalQuarticEval, add_mul, Finset.sum_add_distrib]

theorem rationalQuarticEval_finset_sum {R : Type*} [Field R]
    {g : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ ∑ i ∈ s, f i a b c d) t =
      ∑ i ∈ s, rationalQuarticEval (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rationalQuarticEval]
  | @insert i s hi ih =>
      simp [hi, rationalQuarticEval_add, ih]

theorem rationalQuarticEval_fintype_sum {R : Type*} [Field R]
    {g : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ ∑ i, f i a b c d) t =
      ∑ i, rationalQuarticEval (f i) t := by
  simpa using rationalQuarticEval_finset_sum Finset.univ f t

theorem rationalQuarticEval_sub {R : Type*} [Field R] {g : ℕ}
    (f h : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f a b c d - h a b c d) t =
      rationalQuarticEval f t - rationalQuarticEval h t := by
  simp [rationalQuarticEval, sub_mul, Finset.sum_sub_distrib]

theorem rationalQuarticEval_smul {R : Type*} [Field R] {g : ℕ} (q : R)
    (f : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ q * f a b c d) t =
      q * rationalQuarticEval f t := by
  simp only [rationalQuarticEval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem rationalQuarticEval_symmetrize
    {R : Type*} [Field R] [CharZero R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (symmetrizeQuartic f) t =
      rationalQuarticEval f t := by
  have habdc : rationalQuarticEval (fun a b c d ↦ f a b d c) t =
      rationalQuarticEval f t := rationalQuarticEval_swap23 f t
  have hacbd : rationalQuarticEval (fun a b c d ↦ f a c b d) t =
      rationalQuarticEval f t := rationalQuarticEval_swap12 f t
  have hbacd : rationalQuarticEval (fun a b c d ↦ f b a c d) t =
      rationalQuarticEval f t := rationalQuarticEval_swap01 f t
  have hacdb : rationalQuarticEval (fun a b c d ↦ f a c d b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a b d c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f a b d c) t
      _ = _ := habdc
  have hadbc : rationalQuarticEval (fun a b c d ↦ f a d b c) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a c b d) t := by
        simpa using rationalQuarticEval_swap23 (fun a b c d ↦ f a c b d) t
      _ = _ := hacbd
  have hadcb : rationalQuarticEval (fun a b c d ↦ f a d c b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a d b c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f a d b c) t
      _ = _ := hadbc
  have hbadc : rationalQuarticEval (fun a b c d ↦ f b a d c) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f b a c d) t := by
        simpa using rationalQuarticEval_swap23 (fun a b c d ↦ f b a c d) t
      _ = _ := hbacd
  have hbcad : rationalQuarticEval (fun a b c d ↦ f b c a d) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a c b d) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f a c b d) t
      _ = _ := hacbd
  have hbcda : rationalQuarticEval (fun a b c d ↦ f b c d a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a c d b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f a c d b) t
      _ = _ := hacdb
  have hbdac : rationalQuarticEval (fun a b c d ↦ f b d a c) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f b c a d) t := by
        simpa using rationalQuarticEval_swap23 (fun a b c d ↦ f b c a d) t
      _ = _ := hbcad
  have hbdca : rationalQuarticEval (fun a b c d ↦ f b d c a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f a d c b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f a d c b) t
      _ = _ := hadcb
  have hcabd : rationalQuarticEval (fun a b c d ↦ f c a b d) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f b a c d) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f b a c d) t
      _ = _ := hbacd
  have hcadb : rationalQuarticEval (fun a b c d ↦ f c a d b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f b a d c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f b a d c) t
      _ = _ := hbadc
  have hcbad : rationalQuarticEval (fun a b c d ↦ f c b a d) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f c a b d) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f c a b d) t
      _ = _ := hcabd
  have hcbda : rationalQuarticEval (fun a b c d ↦ f c b d a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f c a d b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f c a d b) t
      _ = _ := hcadb
  have hcdab : rationalQuarticEval (fun a b c d ↦ f c d a b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f b d a c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f b d a c) t
      _ = _ := hbdac
  have hcdba : rationalQuarticEval (fun a b c d ↦ f c d b a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f c d a b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f c d a b) t
      _ = _ := hcdab
  have hdabc : rationalQuarticEval (fun a b c d ↦ f d a b c) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f c a b d) t := by
        simpa using rationalQuarticEval_swap23 (fun a b c d ↦ f c a b d) t
      _ = _ := hcabd
  have hdacb : rationalQuarticEval (fun a b c d ↦ f d a c b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f d a b c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f d a b c) t
      _ = _ := hdabc
  have hdbac : rationalQuarticEval (fun a b c d ↦ f d b a c) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f c b a d) t := by
        simpa using rationalQuarticEval_swap23 (fun a b c d ↦ f c b a d) t
      _ = _ := hcbad
  have hdbca : rationalQuarticEval (fun a b c d ↦ f d b c a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f d a c b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f d a c b) t
      _ = _ := hdacb
  have hdcab : rationalQuarticEval (fun a b c d ↦ f d c a b) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f d b a c) t := by
        simpa using rationalQuarticEval_swap12 (fun a b c d ↦ f d b a c) t
      _ = _ := hdbac
  have hdcba : rationalQuarticEval (fun a b c d ↦ f d c b a) t =
      rationalQuarticEval f t := by
    calc
      _ = rationalQuarticEval (fun a b c d ↦ f d c a b) t := by
        simpa using rationalQuarticEval_swap01 (fun a b c d ↦ f d c a b) t
      _ = _ := hdcab
  rw [show symmetrizeQuartic f = fun a b c d ↦ (1 / 24 : R) *
      (f a b c d + f a b d c + f a c b d + f a c d b + f a d b c + f a d c b +
      f b a c d + f b a d c + f b c a d + f b c d a + f b d a c + f b d c a +
      f c a b d + f c a d b + f c b a d + f c b d a + f c d a b + f c d b a +
      f d a b c + f d a c b + f d b a c + f d b c a + f d c a b + f d c b a) by
    funext a b c d
    simp [symmetrizeQuartic]
    ring]
  rw [rationalQuarticEval_smul]
  simp only [rationalQuarticEval_add]
  rw [habdc, hacbd, hacdb, hadbc, hadcb, hbacd, hbadc, hbcad, hbcda,
    hbdac, hbdca, hcabd, hcadb, hcbad, hcbda, hcdab, hcdba, hdabc,
    hdacb, hdbac, hdbca, hdcab, hdcba]
  ring

def rationalLinearEval {R : Type*} [Field R] {g : ℕ}
    (coeff : Fin g → R) (t : Fin g → R) : R :=
  ∑ a, coeff a * t a

theorem rationalQuadraticEval_product {g : ℕ}
    {R : Type*} [Field R] (f h : Fin g → R) (t : Fin g → R) :
    rationalQuadraticEval (fun a b ↦ f a * h b) t =
      rationalLinearEval f t * rationalLinearEval h t := by
  simp only [rationalQuadraticEval, rationalLinearEval]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem rationalQuarticEval_product {g : ℕ}
    {R : Type*} [Field R] (f h k l : Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ f a * h b * k c * l d) t =
      rationalLinearEval f t * rationalLinearEval h t *
        rationalLinearEval k t * rationalLinearEval l t := by
  simp only [rationalQuarticEval, rationalLinearEval]
  symm
  calc
    (∑ a, f a * t a) * (∑ b, h b * t b) *
          (∑ c, k c * t c) * (∑ d, l d * t d) =
        ((∑ a, f a * t a) * (∑ b, h b * t b)) *
          ((∑ c, k c * t c) * (∑ d, l d * t d)) := by ring
    _ = (∑ a, ∑ b, (f a * t a) * (h b * t b)) *
          (∑ c, ∑ d, (k c * t c) * (l d * t d)) := by
      rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum]
    _ = ∑ a, ∑ c,
          (∑ b, (f a * t a) * (h b * t b)) *
            (∑ d, (k c * t c) * (l d * t d)) := by
      rw [Fintype.sum_mul_sum]
    _ = ∑ a, ∑ c, ∑ b, ∑ d,
          ((f a * t a) * (h b * t b)) *
            ((k c * t c) * (l d * t d)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [Fintype.sum_mul_sum]
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
          f a * h b * k c * l d * t a * t b * t c * t d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring

theorem rationalQuarticEval_quadraticProduct {g : ℕ}
    {R : Type*} [Field R] (q h : Fin g → Fin g → R) (t : Fin g → R) :
    rationalQuarticEval (fun a b c d ↦ q a b * h c d) t =
      rationalQuadraticEval q t * rationalQuadraticEval h t := by
  simp only [rationalQuarticEval, rationalQuadraticEval]
  symm
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

def ratCircuitJacobianCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (i j : Species) (a : Fin g) : ℚ :=
  ∑ r, ratUnitJacobianEntryCoeff C i j r * generator a r

def ratUnitHessianEntryCoeff (C : CodedBimolNetwork)
    (i j l : Species) (r : Fin 5) : ℚ :=
  (codedStoich C i r : ℚ) *
    ∏ s : Species,
      (((C.reaction r).1.decode s).descFactorial
        ((if s = j then 1 else 0) + (if s = l then 1 else 0)) : ℚ)

def ratCircuitHessianCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (i j l : Species) (a : Fin g) : ℚ :=
  ∑ r, ratUnitHessianEntryCoeff C i j l r * generator a r

def ratCircuitRightKernelCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (j : Species) (a : Fin g) : ℚ :=
  if j = 0 then ratCircuitJacobianCoeff C generator 0 1 a
  else -ratCircuitJacobianCoeff C generator 0 0 a

def ratCircuitLeftKernelCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (i : Species) (a : Fin g) : ℚ :=
  if i = 0 then ratCircuitJacobianCoeff C generator 1 0 a
  else -ratCircuitJacobianCoeff C generator 0 0 a

def ratCircuitRawDetCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (a b : Fin g) : ℚ :=
  ratCircuitJacobianCoeff C generator 0 0 a *
      ratCircuitJacobianCoeff C generator 1 1 b -
    ratCircuitJacobianCoeff C generator 0 1 a *
      ratCircuitJacobianCoeff C generator 1 0 b

def ratCircuitDetCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) : Fin g → Fin g → ℚ :=
  symmetrizeQuadratic (ratCircuitRawDetCoeff C generator)

def ratCircuitRawFoldCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (a b c d : Fin g) : ℚ :=
  ∑ i : Species, ∑ j : Species, ∑ l : Species,
    ratCircuitLeftKernelCoeff C generator i a *
      ratCircuitHessianCoeff C generator i j l b *
      ratCircuitRightKernelCoeff C generator j c *
      ratCircuitRightKernelCoeff C generator l d

def ratCircuitFoldCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) :
    Fin g → Fin g → Fin g → Fin g → ℚ :=
  symmetrizeQuartic (ratCircuitRawFoldCoeff C generator)

def ratCircuitResidualCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) :
    Fin g → Fin g → Fin g → Fin g → ℚ :=
  let q := symmetrizeQuadratic detMultiplier
  let product := symmetrizeQuartic fun a b c d ↦
    q a b * ratCircuitDetCoeff C generator c d
  fun a b c d ↦ sign * ratCircuitFoldCoeff C generator a b c d -
    product a b c d

theorem eval_ratCircuitJacobianCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ) (i j : Species) :
    rationalLinearEval
        (fun a ↦ (ratCircuitJacobianCoeff C generator i j a : ℝ)) t =
      C.toNetwork.jacobian
        (circuitCombination (rationalGeneratorReal generator) t)
        unitState i j := by
  simp only [rationalLinearEval, ratCircuitJacobianCoeff]
  push_cast
  simp only [CodedBimolNetwork.toNetwork, SmallPlanarNetwork.jacobian,
    circuitCombination, rationalGeneratorReal, rationalFluxReal]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  fin_cases j <;>
  simp [ratUnitJacobianEntryCoeff,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.unitMultiIndex, SmallPlanarNetwork.stoich,
    codedStoich, unitState,
    Fin.prod_univ_two] <;> ring

theorem eval_ratCircuitHessianCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ)
    (i j l : Species) :
    rationalLinearEval
        (fun a ↦ (ratCircuitHessianCoeff C generator i j l a : ℝ)) t =
      C.toNetwork.hessian
        (circuitCombination (rationalGeneratorReal generator) t)
        unitState i j l := by
  simp only [rationalLinearEval, ratCircuitHessianCoeff]
  push_cast
  simp only [CodedBimolNetwork.toNetwork, SmallPlanarNetwork.hessian,
    circuitCombination, rationalGeneratorReal, rationalFluxReal]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  fin_cases j <;> fin_cases l <;>
  simp [ratUnitHessianEntryCoeff,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.pairMultiIndex, SmallPlanarNetwork.stoich,
    codedStoich, unitState,
    Fin.prod_univ_two] <;> ring

theorem eval_ratCircuitRightKernelCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ) (j : Species) :
    rationalLinearEval
        (fun a ↦ (ratCircuitRightKernelCoeff C generator j a : ℝ)) t =
      canonicalRightKernel C.toNetwork
        (circuitCombination (rationalGeneratorReal generator) t) j := by
  fin_cases j
  · simpa [ratCircuitRightKernelCoeff, canonicalRightKernel] using
      eval_ratCircuitJacobianCoeff C generator t 0 1
  · simpa [ratCircuitRightKernelCoeff, canonicalRightKernel,
      rationalLinearEval] using
      eval_ratCircuitJacobianCoeff C generator t 0 0

theorem eval_ratCircuitLeftKernelCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ) (i : Species) :
    rationalLinearEval
        (fun a ↦ (ratCircuitLeftKernelCoeff C generator i a : ℝ)) t =
      canonicalLeftKernel C.toNetwork
        (circuitCombination (rationalGeneratorReal generator) t) i := by
  fin_cases i
  · simpa [ratCircuitLeftKernelCoeff, canonicalLeftKernel] using
      eval_ratCircuitJacobianCoeff C generator t 1 0
  · simpa [ratCircuitLeftKernelCoeff, canonicalLeftKernel,
      rationalLinearEval] using
      eval_ratCircuitJacobianCoeff C generator t 0 0

theorem eval_ratCircuitDetCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ) :
    rationalQuadraticEval
        (fun a b ↦ (ratCircuitDetCoeff C generator a b : ℝ)) t =
      unitJacobianDet C.toNetwork
        (circuitCombination (rationalGeneratorReal generator) t) := by
  rw [show (fun a b ↦ (ratCircuitDetCoeff C generator a b : ℝ)) =
      symmetrizeQuadratic
        (fun a b ↦ (ratCircuitRawDetCoeff C generator a b : ℝ)) by
    funext a b
    simp [ratCircuitDetCoeff, symmetrizeQuadratic]]
  rw [rationalQuadraticEval_symmetrize]
  rw [show (fun a b ↦ (ratCircuitRawDetCoeff C generator a b : ℝ)) =
      fun a b ↦
        (ratCircuitJacobianCoeff C generator 0 0 a : ℝ) *
            (ratCircuitJacobianCoeff C generator 1 1 b : ℝ) -
          (ratCircuitJacobianCoeff C generator 0 1 a : ℝ) *
            (ratCircuitJacobianCoeff C generator 1 0 b : ℝ) by
    funext a b
    simp [ratCircuitRawDetCoeff]]
  rw [rationalQuadraticEval_sub,
    rationalQuadraticEval_product, rationalQuadraticEval_product,
    eval_ratCircuitJacobianCoeff, eval_ratCircuitJacobianCoeff,
    eval_ratCircuitJacobianCoeff, eval_ratCircuitJacobianCoeff]
  rfl

theorem eval_ratCircuitFoldCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (t : Fin g → ℝ) :
    rationalQuarticEval
        (fun a b c d ↦ (ratCircuitFoldCoeff C generator a b c d : ℝ)) t =
      canonicalFold C.toNetwork
        (circuitCombination (rationalGeneratorReal generator) t) := by
  rw [show (fun a b c d ↦
        (ratCircuitFoldCoeff C generator a b c d : ℝ)) =
      symmetrizeQuartic
        (fun a b c d ↦
          (ratCircuitRawFoldCoeff C generator a b c d : ℝ)) by
    funext a b c d
    simp [ratCircuitFoldCoeff, symmetrizeQuartic]]
  rw [rationalQuarticEval_symmetrize]
  rw [show (fun a b c d ↦
        (ratCircuitRawFoldCoeff C generator a b c d : ℝ)) =
      fun a b c d ↦ ∑ i : Species, ∑ j : Species, ∑ l : Species,
        (ratCircuitLeftKernelCoeff C generator i a : ℝ) *
          (ratCircuitHessianCoeff C generator i j l b : ℝ) *
          (ratCircuitRightKernelCoeff C generator j c : ℝ) *
          (ratCircuitRightKernelCoeff C generator l d : ℝ) by
    funext a b c d
    simp [ratCircuitRawFoldCoeff]]
  rw [rationalQuarticEval_fintype_sum]
  simp only [canonicalFold, dot, SmallPlanarNetwork.hessianApply]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalQuarticEval_fintype_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [rationalQuarticEval_fintype_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [rationalQuarticEval_product,
    eval_ratCircuitLeftKernelCoeff, eval_ratCircuitHessianCoeff,
    eval_ratCircuitRightKernelCoeff, eval_ratCircuitRightKernelCoeff]
  ring

theorem eval_ratCircuitResidualCoeff {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (t : Fin g → ℝ) :
    rationalQuarticEval
        (fun a b c d ↦
          (ratCircuitResidualCoeff C generator sign detMultiplier a b c d : ℝ)) t =
      (sign : ℝ) * canonicalFold C.toNetwork
          (circuitCombination (rationalGeneratorReal generator) t) -
        rationalQuadraticEval
            (fun a b ↦ (detMultiplier a b : ℝ)) t *
          unitJacobianDet C.toNetwork
            (circuitCombination (rationalGeneratorReal generator) t) := by
  rw [show (fun a b c d ↦
        (ratCircuitResidualCoeff C generator sign detMultiplier a b c d : ℝ)) =
      fun a b c d ↦
        (sign : ℝ) * (ratCircuitFoldCoeff C generator a b c d : ℝ) -
          symmetrizeQuartic (fun a b c d ↦
            symmetrizeQuadratic
                (fun a b ↦ (detMultiplier a b : ℝ)) a b *
              (ratCircuitDetCoeff C generator c d : ℝ)) a b c d by
    funext a b c d
    simp [ratCircuitResidualCoeff, symmetrizeQuadratic,
      symmetrizeQuartic]]
  rw [rationalQuarticEval_sub, rationalQuarticEval_smul,
    rationalQuarticEval_symmetrize, rationalQuarticEval_quadraticProduct,
    rationalQuadraticEval_symmetrize, eval_ratCircuitFoldCoeff,
    eval_ratCircuitDetCoeff]

theorem reflectedRationalCircuitFoldCertificate_excludes_cusp {g : ℕ}
    (C : CodedBimolNetwork) (generator : Fin g → Fin 5 → ℚ)
    (sign : ℚ) (detMultiplier : Fin g → Fin g → ℚ)
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hcoeff : ∀ a b c d,
      0 ≤ ratCircuitResidualCoeff C generator sign detMultiplier a b c d)
    (hstrictSupport : ∀ active : Finset (Fin g),
      (∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r) →
      ∃ a ∈ active, ∃ b ∈ active, ∃ c ∈ active, ∃ d ∈ active,
        0 < ratCircuitResidualCoeff C generator sign detMultiplier a b c d) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply rationalCircuitFoldCertificate_excludes_cusp_of_rational
    C generator sign
      (ratCircuitResidualCoeff C generator sign detMultiplier)
      detMultiplier hcircuits hgenerator hcoeff hstrictSupport
  intro t
  change (sign : ℝ) * canonicalFold C.toNetwork
        (circuitCombination (rationalGeneratorReal generator) t) =
      rationalQuarticEval
          (fun a b c d ↦
            (ratCircuitResidualCoeff C generator sign detMultiplier a b c d : ℝ)) t +
        rationalQuadraticEval
            (fun a b ↦ (detMultiplier a b : ℝ)) t *
          unitJacobianDet C.toNetwork
            (circuitCombination (rationalGeneratorReal generator) t)
  rw [eval_ratCircuitResidualCoeff]
  ring

structure QuarticWitness (g : ℕ) where
  a : Fin g
  b : Fin g
  c : Fin g
  d : Fin g
deriving DecidableEq, Fintype

def QuarticWitness.swap01 {g : ℕ} (w : QuarticWitness g) : QuarticWitness g :=
  ⟨w.b, w.a, w.c, w.d⟩

def QuarticWitness.swap12 {g : ℕ} (w : QuarticWitness g) : QuarticWitness g :=
  ⟨w.a, w.c, w.b, w.d⟩

def QuarticWitness.swap23 {g : ℕ} (w : QuarticWitness g) : QuarticWitness g :=
  ⟨w.a, w.b, w.d, w.c⟩

def QuarticWitness.compare01 {g : ℕ} (w : QuarticWitness g) :
    QuarticWitness g :=
  if w.a ≤ w.b then w else w.swap01

def QuarticWitness.compare12 {g : ℕ} (w : QuarticWitness g) :
    QuarticWitness g :=
  if w.b ≤ w.c then w else w.swap12

def QuarticWitness.compare23 {g : ℕ} (w : QuarticWitness g) :
    QuarticWitness g :=
  if w.c ≤ w.d then w else w.swap23

def QuarticWitness.sort {g : ℕ} (w : QuarticWitness g) : QuarticWitness g :=
  let w1 := w.compare01
  let w2 := w1.compare12
  let w3 := w2.compare23
  let w4 := w3.compare01
  let w5 := w4.compare12
  w5.compare01

def QuarticWitness.Sorted {g : ℕ} (w : QuarticWitness g) : Prop :=
  w.a ≤ w.b ∧ w.b ≤ w.c ∧ w.c ≤ w.d

instance {g : ℕ} (w : QuarticWitness g) : Decidable w.Sorted := by
  unfold QuarticWitness.Sorted
  infer_instance

theorem QuarticWitness.sort_sorted {g : ℕ} (w : QuarticWitness g) :
    w.sort.Sorted := by
  simp only [QuarticWitness.sort, QuarticWitness.compare01,
    QuarticWitness.compare12, QuarticWitness.compare23,
    QuarticWitness.swap01, QuarticWitness.swap12, QuarticWitness.swap23,
    QuarticWitness.Sorted]
  split_ifs <;> simp_all <;> omega

theorem symmetrizeQuartic_swap01_point {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (a b c d : Fin g) :
    symmetrizeQuartic f b a c d = symmetrizeQuartic f a b c d := by
  simp [symmetrizeQuartic]
  ring

theorem symmetrizeQuartic_swap12_point {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (a b c d : Fin g) :
    symmetrizeQuartic f a c b d = symmetrizeQuartic f a b c d := by
  simp [symmetrizeQuartic]
  ring

theorem symmetrizeQuartic_swap23_point {R : Type*} [Field R] {g : ℕ}
    (f : Fin g → Fin g → Fin g → Fin g → R) (a b c d : Fin g) :
    symmetrizeQuartic f a b d c = symmetrizeQuartic f a b c d := by
  simp [symmetrizeQuartic]
  ring

theorem ratCircuitResidualCoeff_swap01 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (a b c d : Fin g) :
    ratCircuitResidualCoeff C generator sign detMultiplier b a c d =
      ratCircuitResidualCoeff C generator sign detMultiplier a b c d := by
  simp only [ratCircuitResidualCoeff, ratCircuitFoldCoeff]
  rw [show symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) b a c d =
      symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) a b c d from
        symmetrizeQuartic_swap01_point _ a b c d]
  rw [show symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) b a c d =
      symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) a b c d from
        symmetrizeQuartic_swap01_point _ a b c d]

theorem ratCircuitResidualCoeff_swap12 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (a b c d : Fin g) :
    ratCircuitResidualCoeff C generator sign detMultiplier a c b d =
      ratCircuitResidualCoeff C generator sign detMultiplier a b c d := by
  simp only [ratCircuitResidualCoeff, ratCircuitFoldCoeff]
  rw [show symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) a c b d =
      symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) a b c d from
        symmetrizeQuartic_swap12_point _ a b c d]
  rw [show symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) a c b d =
      symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) a b c d from
        symmetrizeQuartic_swap12_point _ a b c d]

theorem ratCircuitResidualCoeff_swap23 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (a b c d : Fin g) :
    ratCircuitResidualCoeff C generator sign detMultiplier a b d c =
      ratCircuitResidualCoeff C generator sign detMultiplier a b c d := by
  simp only [ratCircuitResidualCoeff, ratCircuitFoldCoeff]
  rw [show symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) a b d c =
      symmetrizeQuartic (ratCircuitRawFoldCoeff C generator) a b c d from
        symmetrizeQuartic_swap23_point _ a b c d]
  rw [show symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) a b d c =
      symmetrizeQuartic (fun a b c d ↦
        symmetrizeQuadratic detMultiplier a b *
          ratCircuitDetCoeff C generator c d) a b c d from
        symmetrizeQuartic_swap23_point _ a b c d]

theorem ratCircuitResidualCoeff_compare01 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (w : QuarticWitness g) :
    ratCircuitResidualCoeff C generator sign detMultiplier
        w.compare01.a w.compare01.b w.compare01.c w.compare01.d =
      ratCircuitResidualCoeff C generator sign detMultiplier w.a w.b w.c w.d := by
  by_cases h : w.a ≤ w.b
  · simp [QuarticWitness.compare01, h]
  · simp [QuarticWitness.compare01, h, QuarticWitness.swap01,
      ratCircuitResidualCoeff_swap01]

theorem ratCircuitResidualCoeff_compare12 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (w : QuarticWitness g) :
    ratCircuitResidualCoeff C generator sign detMultiplier
        w.compare12.a w.compare12.b w.compare12.c w.compare12.d =
      ratCircuitResidualCoeff C generator sign detMultiplier w.a w.b w.c w.d := by
  by_cases h : w.b ≤ w.c
  · simp [QuarticWitness.compare12, h]
  · simp [QuarticWitness.compare12, h, QuarticWitness.swap12,
      ratCircuitResidualCoeff_swap12]

theorem ratCircuitResidualCoeff_compare23 {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (w : QuarticWitness g) :
    ratCircuitResidualCoeff C generator sign detMultiplier
        w.compare23.a w.compare23.b w.compare23.c w.compare23.d =
      ratCircuitResidualCoeff C generator sign detMultiplier w.a w.b w.c w.d := by
  by_cases h : w.c ≤ w.d
  · simp [QuarticWitness.compare23, h]
  · simp [QuarticWitness.compare23, h, QuarticWitness.swap23,
      ratCircuitResidualCoeff_swap23]

theorem ratCircuitResidualCoeff_sort {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ) (w : QuarticWitness g) :
    ratCircuitResidualCoeff C generator sign detMultiplier
        w.sort.a w.sort.b w.sort.c w.sort.d =
      ratCircuitResidualCoeff C generator sign detMultiplier w.a w.b w.c w.d := by
  simp only [QuarticWitness.sort]
  rw [ratCircuitResidualCoeff_compare01, ratCircuitResidualCoeff_compare12,
    ratCircuitResidualCoeff_compare01, ratCircuitResidualCoeff_compare23,
    ratCircuitResidualCoeff_compare12, ratCircuitResidualCoeff_compare01]

theorem reflectedRationalCircuitFoldCertificate_excludes_cusp_of_witnesses
    {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ)
    (witnesses : Finset (QuarticWitness g))
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hcoeff : ∀ a b c d,
      0 ≤ ratCircuitResidualCoeff C generator sign detMultiplier a b c d)
    (hpositive : ∀ w ∈ witnesses,
      0 < ratCircuitResidualCoeff C generator sign detMultiplier
        w.a w.b w.c w.d)
    (hcover : ∀ active : Finset (Fin g),
      (∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r) →
      ∃ w ∈ witnesses,
        w.a ∈ active ∧ w.b ∈ active ∧ w.c ∈ active ∧ w.d ∈ active) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp
    C generator sign detMultiplier hcircuits hgenerator hcoeff
  intro active hactive
  obtain ⟨w, hw, ha, hb, hc, hd⟩ := hcover active hactive
  exact ⟨w.a, ha, w.b, hb, w.c, hc, w.d, hd, hpositive w hw⟩

theorem reflectedRationalCircuitFoldCertificate_excludes_cusp_of_sorted_witnesses
    {g : ℕ} (C : CodedBimolNetwork)
    (generator : Fin g → Fin 5 → ℚ) (sign : ℚ)
    (detMultiplier : Fin g → Fin g → ℚ)
    (witnesses : Finset (QuarticWitness g))
    (hcircuits : rationalCircuitFinset C = Finset.univ.image generator)
    (hgenerator : Function.Injective generator)
    (hsorted : ∀ w : QuarticWitness g, w.Sorted →
      0 ≤ ratCircuitResidualCoeff C generator sign detMultiplier
        w.a w.b w.c w.d)
    (hpositive : ∀ w ∈ witnesses,
      0 < ratCircuitResidualCoeff C generator sign detMultiplier
        w.a w.b w.c w.d)
    (hcover : ∀ active : Finset (Fin g),
      (∀ r : Fin 5, ∃ a ∈ active, 0 < generator a r) →
      ∃ w ∈ witnesses,
        w.a ∈ active ∧ w.b ∈ active ∧ w.c ∈ active ∧ w.d ∈ active) :
    ¬ AdmitsTransverseCusp C.toNetwork := by
  apply reflectedRationalCircuitFoldCertificate_excludes_cusp_of_witnesses
    C generator sign detMultiplier witnesses hcircuits hgenerator
  · intro a b c d
    let w : QuarticWitness g := ⟨a, b, c, d⟩
    rw [← ratCircuitResidualCoeff_sort C generator sign detMultiplier w]
    exact hsorted w.sort w.sort_sorted
  · exact hpositive
  · exact hcover

end SmallCusp

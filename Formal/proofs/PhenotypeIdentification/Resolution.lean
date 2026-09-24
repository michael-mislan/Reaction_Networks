import Mathlib

/-! Finite algebra only. The chronological source, matrix logarithm,
and statistical arguments are proved conventionally in the manuscript. -/
namespace PhenotypeIdentification

def response (a : ℚ) (x : Bool) : ℚ := if x then a else 1 - a

def pairLaw (p a b : ℚ) (x y : Bool) : ℚ :=
  (1-p) * response a x * response a y + p * response b x * response b y

theorem pair_alias :
    pairLaw (1/2) (3/10) (7/10) = pairLaw (1/5) (2/5) (9/10) := by
  funext x y
  cases x <;> cases y <;> norm_num [pairLaw, response]

theorem triple_separation :
    ((1-(1/5 : ℚ))*(2/5)^3+(1/5)*(9/10)^3) -
    ((1-(1/2 : ℚ))*(3/10)^3+(1/2)*(7/10)^3) = 3/250 := by
  norm_num

theorem every_pair_decision (f : Bool → Bool → ℚ) :
    (∑ x : Bool, ∑ y : Bool, pairLaw (1/2) (3/10) (7/10) x y * f x y) =
    (∑ x : Bool, ∑ y : Bool, pairLaw (1/5) (2/5) (9/10) x y * f x y) := by
  rw [pair_alias]

theorem mixture_preparation_alias (p a b a' b' : ℝ) (hne : b' - a' ≠ 0) :
    let p' := ((1-p)*a+p*b-a')/(b'-a')
    (1-p')*a'+p'*b' = (1-p)*a+p*b := by
  dsimp
  field_simp
  nlinarith

theorem emission_recovery {n : Type*} [Fintype n] [DecidableEq n]
    (L E M : Matrix n n ℝ) (h : L * E = 1) :
    L * (E * M * E.transpose) * L.transpose = M := by
  have ht : E.transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, h, Matrix.transpose_one]
  calc
    L * (E * M * E.transpose) * L.transpose =
        (L * E) * M * (E.transpose * L.transpose) := by
          simp only [Matrix.mul_assoc]
    _ = M := by rw [h, ht, Matrix.one_mul, Matrix.mul_one]

theorem exit_recovery {n : Type*} [Fintype n] [DecidableEq n]
    (V W D B : Matrix n n ℝ) (h : V * W = 1) (hd : D = W * B) :
    V * D = B := by
  rw [hd, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem correlated_kernel_marginals (x y z t : ℝ) :
    (x+t)+(y-t)=x+y ∧ (y-t)+(z+t)=y+z := by
  constructor <;> ring

theorem correlated_kernel_joint_change (z t : ℝ) : (z+t)-z=t := by ring

theorem aggregate_finite_component :
    pairLaw (1/2) (3/10) (7/10) = pairLaw (1/5) (2/5) (9/10) ∧
    ((1-(1/5 : ℚ))*(2/5)^3+(1/5)*(9/10)^3) -
      ((1-(1/2 : ℚ))*(3/10)^3+(1/2)*(7/10)^3) = 3/250 :=
  ⟨pair_alias, triple_separation⟩

end PhenotypeIdentification

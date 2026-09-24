import Mathlib
import proofs.TypeIIL.GeneralSeparator
import proofs.TypeIIL.CyclicSign

namespace TypeIIL

abbrev Species (l : ℕ) := Sum (Fin l) (Fin l)
abbrev Reaction (l : ℕ) := Sum (Fin l) (Fin l)

/-- Strict-gap Type II_l source data.  `E j` is fork `j`, `S j` is its back
product, and `next` records the cyclicly next fork. -/
structure StrictData (l : ℕ) where
  next : Fin l ≃ Fin l
  next_singleCycle : IsSingleCycle next
  m : Fin l → ℕ
  m_pos : ∀ j, 0 < m j

def strictStoich (d : StrictData l) : Species l → Reaction l → ℝ
  | .inl i, .inl j => if i = j then -1 else 0
  | .inl i, .inr j => if i = j then 1 else 0
  | .inr i, .inl j =>
      (if i = j then 1 else 0) + (if i = d.next j then d.m j else 0)
  | .inr i, .inr j => if i = j then -1 else 0

def strictAlpha (rho : Species l → ℝ) : Reaction l → ℝ
  | .inl j => rho (.inl j)
  | .inr j => rho (.inr j)

def strictBeta (d : StrictData l) (rho : Species l → ℝ) : Reaction l → ℝ
  | .inl j => rho (.inr j) * rho (.inr (d.next j)) ^ d.m j
  | .inr j => rho (.inl j)

def AllRatiosOne (rho : Species l → ℝ) : Prop := ∀ i, rho i = 1

/-- The exact remaining combinatorial interface: every non-unit positive ratio
vector has a Gordan separator for the strict-gap source matrix. -/
def StrictSeparatorComplete (d : StrictData l) : Prop :=
  ∀ rho : Species l → ℝ, (∀ i, 0 < rho i) → ¬ AllRatiosOne rho →
    Nonempty (KernelSeparator (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho)

/-- Once the cyclic separator exists, a strictly positive two-root kernel has
only the unit concentration ratio. -/
theorem strict_positive_kernel_ratios_all_one
    (d : StrictData l) (hcomplete : StrictSeparatorComplete d)
    (rho : Species l → ℝ)
    (p q : Reaction l → ℝ) (e : Species l → ℝ)
    (hrho : ∀ i, 0 < rho i)
    (hp : ∀ j, 0 < p j) (hq : ∀ j, 0 < q j) (he : ∀ i, 0 < e i)
    (hB : TypeII3.BaseFluxBalance (strictStoich d) p q e)
    (hR : TypeII3.RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e) :
    AllRatiosOne rho := by
  by_contra hnot
  rcases hcomplete rho hrho hnot with ⟨s⟩
  exact no_positive_kernel_of_separator
    (strictStoich d) (strictAlpha rho) (strictBeta d rho) rho p q e
    hp hq he hB hR s

end TypeIIL

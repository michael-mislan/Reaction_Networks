import proofs.CommonPhysicalRealization.ExporterThermochemistry

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding

/-- Parameterize a supported neighboring pair by its nonnegative surplus counts. -/
def beforePair (n : Counts) (j : Fin 6) : Counts :=
  fun i => n i+pairLeft j (i.castLE (by decide))
def afterPair (n : Counts) (j : Fin 6) : Counts :=
  fun i => n i+pairRight j (i.castLE (by decide))

def neighborFactor (n : Counts) (V : ℝ) : Fin 6 → ℝ :=
  ![((n 0:ℝ)+1)*((n 1:ℝ)+1)/(V*((n 2:ℝ)+1)),
    ((n 0:ℝ)+1)*((n 2:ℝ)+1)/(V*((n 3:ℝ)+1)),
    ((n 1:ℝ)+1)*((n 3:ℝ)+1)/(V*((n 4:ℝ)+1)),
    ((n 4:ℝ)+1)/((n 5:ℝ)+1),
    V*((n 5:ℝ)+1)/(((n 2:ℝ)+2)*((n 2:ℝ)+1)),
    V*((n 2:ℝ)+1)/(((n 0:ℝ)+1)*((n 1:ℝ)+1))]

theorem neighboring_rate_ratio (n : Counts) (V r d : ℝ)
    (hV : 0 < V) (hr : 0 < r) (hd : 0 < d) (j : Fin 6) :
    physicalRate (beforePair n j) V r d 1 1 (pairForward j) /
      physicalRate (afterPair n j) V r d 1 1 (pairReverse j) =
        forwardCoefficient r d j / reverseCoefficient r d j * neighborFactor n V j := by
  have hn (i : Fin 6) : 0 ≤ (n i:ℝ) := Nat.cast_nonneg _
  have h1 (i : Fin 6) : (n i:ℝ)+1 ≠ 0 := by positivity
  have h2 (i : Fin 6) : (n i:ℝ)+2 ≠ 0 := by positivity
  fin_cases j <;>
    simp [physicalRate,beforePair,afterPair,pairLeft,pairRight,pairForward,pairReverse,
      forwardCoefficient,reverseCoefficient,neighborFactor,Nat.cast_add,Nat.cast_mul] <;>
    field_simp [ne_of_gt hV,ne_of_gt hr,ne_of_gt hd,h1,h2]

end
end CommonPhysicalRealization



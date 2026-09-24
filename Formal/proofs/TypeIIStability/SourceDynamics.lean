import proofs.TypeIIStability.RawSource

namespace TypeIIStability.Witness
noncomputable section
open TypeIIL TypeII3
open TypeIIStability.Source
open MixedDegradation.TypeII
open scoped Matrix BigOperators
set_option maxRecDepth 1024
set_option maxHeartbeats 1600000

def physicalCurrent (z : Fin 7 → ℝ) (i : Fin 7) : ℝ :=
  forwardRate i*z i-reverseRate i*products z i

theorem active_current_general (z : Fin 7 → ℝ) (j : Fin 3) :
    current sourceRates (fun i => z i.castSucc) (fork6 j) = physicalCurrent z (fork6 j).castSucc := by
  have hplus : sourceRates.plus (fork6 j) = forwardRate (fork6 j).castSucc := by fin_cases j <;> rfl
  have hminus : sourceRates.minus (fork6 j) = reverseRate (fork6 j).castSucc := by fin_cases j <;> rfl
  simp only [current, hplus, hminus, active_product, physicalCurrent]

/-- Retained equations from the existing source presentation, removing the
 synthetic return columns and inserting both literal endpoint currents. -/
def sourceCoreDrift (z : Fin 7 → ℝ) (i : Fin 6) : ℝ :=
  (∑ r, sourceStoich next6 (fun _ => 1) back6 i r*current sourceRates (fun k => z k.castSucc) r) -
    (∑ j, sourceStoich next6 (fun _ => 1) back6 i (skeleton.paperTailTerminal j)*
      current sourceRates (fun k => z k.castSucc) (skeleton.paperTailTerminal j)) +
    (∑ j, skeleton.paperTailBoundaryContribution i j
      (![physicalCurrent z 5, physicalCurrent z 1, physicalCurrent z 3] j)
      (![physicalCurrent z 5, physicalCurrent z 6, physicalCurrent z 3] j)) -
    sourceRates.degrade i*z i.castSucc

/-- Full source dynamics, retaining the internal return-path state. The
 return rates are exactly those used to construct `returnChain`. -/
def sourceDrift (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![sourceCoreDrift z 0, sourceCoreDrift z 1, sourceCoreDrift z 2,
    sourceCoreDrift z 3, sourceCoreDrift z 4, sourceCoreDrift z 5,
    physicalCurrent z 1-physicalCurrent z 6-degradation 6*z 6]

theorem sourceCoreDrift_formula (z : Fin 7 → ℝ) (i : Fin 6) :
    sourceCoreDrift z i =
      ![-physicalCurrent z 0+physicalCurrent z 5,
        physicalCurrent z 0+physicalCurrent z 2-physicalCurrent z 1,
        -physicalCurrent z 2+physicalCurrent z 6,
        physicalCurrent z 2+physicalCurrent z 4-physicalCurrent z 3,
        -physicalCurrent z 4+physicalCurrent z 3,
        physicalCurrent z 0+physicalCurrent z 4-physicalCurrent z 5] i -
      degradation i.castSucc*z i.castSucc := by
  unfold sourceCoreDrift
  rw [retained_balance_formula]
  have h0 := active_current_general z 0
  have h1 := active_current_general z 1
  have h2 := active_current_general z 2
  change current sourceRates (fun k => z k.castSucc) 0 = physicalCurrent z 0 at h0
  change current sourceRates (fun k => z k.castSucc) 2 = physicalCurrent z 2 at h1
  change current sourceRates (fun k => z k.castSucc) 4 = physicalCurrent z 4 at h2
  simp only [h0, h1, h2]
  have hd : sourceRates.degrade i = degradation i.castSucc := rfl
  rw [hd]
  fin_cases i <;> rfl

theorem source_drift_eq (z : Fin 7 → ℝ) : sourceDrift z = drift z := by
  have hcast : ∀ k : Fin 6, k.castSucc = (![0,1,2,3,4,5] : Fin 6 → Fin 7) k := by
    intro k; fin_cases k <;> rfl
  ext i
  fin_cases i <;>
    simp [sourceDrift, sourceCoreDrift_formula, hcast, drift, physicalCurrent,
      N, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ] <;> ring

theorem source_physical_derivative :
    HasFDerivAt sourceDrift (MixedDegradation.matrixCLM A) x := by
  have h : sourceDrift = drift := funext source_drift_eq
  rw [h]
  exact physical_derivative

end
end TypeIIStability.Witness

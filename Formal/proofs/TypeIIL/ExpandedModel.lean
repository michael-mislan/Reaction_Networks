import Mathlib
import proofs.TypeIIL.StrictAdapter
import proofs.TypeII3.Network.ChainCompression

namespace TypeIIL

open TypeII3

/-- A source-faithful family of positive unit-stoichiometric intervals between
successive fork/back endpoints. -/
structure ExpandedData (l : ℕ) extends StrictData l where
  chain : Fin l → UnitChain

/-- Two positive equilibria of an expanded strict Type II_l core, written in
flux coordinates.  `Y` is the reference endpoint state and `rho*Y` the second
endpoint state; `z0,z1` are the corresponding internal chain states. -/
structure ExpandedTwoRoot [NeZero l] (D : ExpandedData l) where
  YS : Fin l → ℝ
  YE : Fin l → ℝ
  rhoS : Fin l → ℝ
  rhoE : Fin l → ℝ
  pF : Fin l → ℝ
  qF : Fin l → ℝ
  degS : Fin l → ℝ
  degE : Fin l → ℝ
  z0 : ∀ j, (D.chain j).State
  z1 : ∀ j, (D.chain j).State
  jL0 : Fin l → ℝ
  jR0 : Fin l → ℝ
  jL1 : Fin l → ℝ
  jR1 : Fin l → ℝ
  YS_pos : ∀ j, 0 < YS j
  YE_pos : ∀ j, 0 < YE j
  rhoS_pos : ∀ j, 0 < rhoS j
  rhoE_pos : ∀ j, 0 < rhoE j
  pF_pos : ∀ j, 0 < pF j
  qF_pos : ∀ j, 0 < qF j
  degS_pos : ∀ j, 0 < degS j
  degE_pos : ∀ j, 0 < degE j
  chain0 : ∀ j, ChainFlux (D.chain j) (z0 j) (YS j) (YE j)
    (jL0 j) (jR0 j)
  chain1 : ∀ j, ChainFlux (D.chain j) (z1 j)
    (rhoS j * YS j) (rhoE j * YE j) (jL1 j) (jR1 j)
  baseE : ∀ j, -(pF j - qF j) + jR0 j - degE j * YE j = 0
  baseS : ∀ j, (pF j - qF j) +
    D.m (D.next.symm j) * (pF (D.next.symm j) - qF (D.next.symm j)) -
      jL0 j - degS j * YS j = 0
  ratioE : ∀ j,
    -(rhoE j * pF j - (rhoS j * rhoS (D.next j) ^ D.m j) * qF j) +
      jR1 j - degE j * (rhoE j * YE j) = 0
  ratioS : ∀ j,
    (rhoE j * pF j - (rhoS j * rhoS (D.next j) ^ D.m j) * qF j) +
      D.m (D.next.symm j) *
        (rhoE (D.next.symm j) * pF (D.next.symm j) -
          (rhoS (D.next.symm j) * rhoS j ^ D.m (D.next.symm j)) *
            qF (D.next.symm j)) -
      jL1 j - degS j * (rhoS j * YS j) = 0

def ExpandedData.strict (D : ExpandedData l) : StrictData l := D.toStrictData

theorem expanded_typeII_ratios_all_one [NeZero l]
    (D : ExpandedData l) (W : ExpandedTwoRoot D) :
    (∀ j, W.rhoS j = 1) ∧ (∀ j, W.rhoE j = 1) ∧
      (∀ j, W.z0 j = W.z1 j) := by
  let d := D.strict
  let rho : Species l → ℝ := fun
    | .inl j => W.rhoE j
    | .inr j => W.rhoS j
  let p : Reaction l → ℝ := fun
    | .inl j => W.pF j
    | .inr j => (D.chain j).summary.c * W.YS j
  let q : Reaction l → ℝ := fun
    | .inl j => W.qF j
    | .inr j => (D.chain j).summary.beta * W.YE j
  let e : Species l → ℝ := fun
    | .inl j => (W.degE j + (D.chain j).summary.leakR) * W.YE j
    | .inr j => (W.degS j + (D.chain j).summary.leakL) * W.YS j
  have hc0 := fun j => chain_flux_compress (D.chain j) (W.z0 j) (W.chain0 j)
  have hc1 := fun j => chain_flux_compress (D.chain j) (W.z1 j) (W.chain1 j)
  have hp : ∀ r, 0 < p r := by
    intro r; cases r with
    | inl j => exact W.pF_pos j
    | inr j => exact mul_pos (D.chain j).summary.c_pos (W.YS_pos j)
  have hq : ∀ r, 0 < q r := by
    intro r; cases r with
    | inl j => exact W.qF_pos j
    | inr j => exact mul_pos (D.chain j).summary.beta_pos (W.YE_pos j)
  have he : ∀ i, 0 < e i := by
    intro i; cases i with
    | inl j => exact mul_pos (add_pos_of_pos_of_nonneg (W.degE_pos j)
        (D.chain j).summary.leakR_nonneg) (W.YE_pos j)
    | inr j => exact mul_pos (add_pos_of_pos_of_nonneg (W.degS_pos j)
        (D.chain j).summary.leakL_nonneg) (W.YS_pos j)
  have hB : BaseFluxBalance (strictStoich d) p q e := by
    intro i
    cases i with
    | inl j =>
        rw [strictStoich_fork_sum]
        dsimp [p, q, e]
        have hc := (hc0 j).2
        linear_combination W.baseE j - hc
    | inr j =>
        rw [strictStoich_back_sum]
        dsimp [p, q, e, d, ExpandedData.strict]
        have hc := (hc0 j).1
        linear_combination W.baseS j + hc
  have hR : RatioFluxBalance (strictStoich d)
      (strictAlpha rho) (strictBeta d rho) rho p q e := by
    intro i
    cases i with
    | inl j =>
        rw [strictStoich_fork_sum]
        dsimp [strictAlpha, strictBeta, rho, p, q, e, d, ExpandedData.strict]
        have hc := (hc1 j).2
        linear_combination W.ratioE j - hc
    | inr j =>
        rw [strictStoich_back_sum]
        dsimp [strictAlpha, strictBeta, rho, p, q, e, d, ExpandedData.strict]
        have hc := (hc1 j).1
        have hw := W.ratioS j
        simp only [D.next.apply_symm_apply] at hw ⊢
        linear_combination hw + hc
  have hrho : ∀ i, 0 < rho i := by
    intro i; cases i with
    | inl j => exact W.rhoE_pos j
    | inr j => exact W.rhoS_pos j
  have hall := strict_positive_kernel_ratios_all_one_unconditional
    d rho p q e hrho hp hq he hB hR
  have hS : ∀ j, W.rhoS j = 1 := fun j => hall (.inr j)
  have hE : ∀ j, W.rhoE j = 1 := fun j => hall (.inl j)
  refine ⟨hS, hE, ?_⟩
  intro j
  apply chain_state_unique (D.chain j) (W.z0 j) (W.z1 j) (W.chain0 j)
  simpa [hS j, hE j] using W.chain1 j

end TypeIIL

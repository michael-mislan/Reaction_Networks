import proofs.StoredRedCells.S7Application
import proofs.StoredRedCells.S7Certificate

/-! Concrete full-source physical inventory bound. This file must be verified
after the complete source-data assembly; no biological admissibility is asserted.
The objective and supply vectors are the explicit source certificate fields. -/
namespace StoredRedCells.S7Certificate
noncomputable section

-- Symbolic docking uses the checked interfaces; do not unfold the entire data.
attribute [local irreducible] sourceChunks sourceTotal

abbrev SourceReaction := Fin sourceChunks.flatten.length
def sourceColumn : SourceReaction → Column := columnAt sourceChunks
def weightScale : ℝ := 403619500
def stoichiometryScale : ℝ := 10000000000000000
def boundScale : ℝ := 5000000000000000000000

theorem source_joint_inventory_bound
    (xi : SourceReaction → ℝ) (x0 ell : Fin 10411 → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hfloor : ∀ i, (chemicalWeight i.val : ℝ) ≠ 0 →
      ell i ≤ x0 i + ∑ j, (matrixEntry (sourceColumn j) i / stoichiometryScale) * xi j)
    (haux : ∀ i, (auxiliaryWeight i.val : ℝ) ≠ 0 →
      ∑ j, (matrixEntry (sourceColumn j) i / stoichiometryScale) * xi j = 0)
    (hL : ∀ j, ((sourceColumn j).lower : ℝ) / boundScale * T ≤ xi j)
    (hU : ∀ j, xi j ≤ ((sourceColumn j).upper : ℝ) / boundScale * T) :
    (∑ j, (((sourceColumn j).objective : ℝ) / (weightScale*stoichiometryScale)) * xi j) ≤
      (∑ i, ((chemicalWeight i.val : ℝ) / weightScale) * (x0 i - ell i)) +
      (25439042 / 1000000 : ℝ)*T +
      (∑ j, (((sourceColumn j).supply : ℝ) / (weightScale*stoichiometryScale)) *
        max (-xi j) 0) := by
  have hexact : (sourceTotal : ℝ) / 20180975000000000000000000000000000000000000000 =
      (1283461673726143619667945455169487587 /
        50452437500000000000000000000000000 : ℝ) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) source_cost_exact
    push_cast at h
    exact h
  have hround : (1283461673726143619667945455169487587 /
      50452437500000000000000000000000000 : ℝ) ≤ 25439042 / 1000000 := by
    norm_num
  have hden : weightScale*stoichiometryScale*boundScale =
      20180975000000000000000000000000000000000000000 := by
    norm_num [weightScale, stoichiometryScale, boundScale]
  have hcost :
      (((sourceChunks.map (fun rs => (rs.map cost).sum)).sum : ℤ) : ℝ) /
        (weightScale*stoichiometryScale*boundScale) ≤ 25439042 / 1000000 := by
    rw [hden]
    simpa only [sourceTotal] using hexact.le.trans hround
  exact inventory_from_chunks sourceChunks xi x0 ell T
    weightScale stoichiometryScale boundScale (25439042/1000000)
    (by norm_num [weightScale]) (by norm_num [stoichiometryScale])
    (by norm_num [boundScale]) source_indices_valid source_supplies_nonnegative
    hcost hT hfloor haux hL hU

end
end StoredRedCells.S7Certificate

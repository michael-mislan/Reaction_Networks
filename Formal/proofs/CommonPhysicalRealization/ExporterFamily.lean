import proofs.CommonPhysicalRealization.ExporterThermochemistry
import proofs.CommonPhysicalRealization.ExporterProductiveState
import proofs.RandomViability.BindingCompetitionContractModel

namespace CommonPhysicalRealization
noncomputable section
open RandomViability.Binding

def physicalRectangle : Set (ℝ × ℝ) := Set.Icc (19,1/50) (21,1/25)

theorem rectangle_compact : IsCompact physicalRectangle := isCompact_Icc

theorem rectangle_interior_point : (20,3/100) ∈ physicalRectangle := by
  norm_num [physicalRectangle,Set.mem_Icc,Prod.le_def]

def donorParameters (p : physicalRectangle) : CompetitionRateBox where
  K := 10
  r := p.val.1
  delta := p.val.2
  K_lower := by norm_num
  K_upper := by norm_num
  r_lower := by have := p.property.1.1; linarith
  r_upper := by have := p.property.2.1; linarith
  delta_lower := by have := p.property.1.2; linarith
  delta_upper := by have := p.property.2.2; linarith

theorem family_thermochemistry (p : physicalRectangle) (j : Fin 6) :
    0 < forwardCoefficient p.val.1 p.val.2 j ∧
    0 < reverseCoefficient p.val.1 p.val.2 j ∧
    Real.log (forwardCoefficient p.val.1 p.val.2 j / reverseCoefficient p.val.1 p.val.2 j) =
      ∑ i, ((pairLeft j i : ℝ)-pairRight j i)*standardPotential i := by
  apply common_thermochemistry
  · have := p.property.1.1; linarith
  · have := p.property.1.2; linarith

theorem family_productive (p : physicalRectangle) (i : Fin 4) :
    0 < productiveDrift p.val.1 p.val.2 i :=
  productive_positive _ _ p.property.1.1 p.property.2.1 p.property.2.2 i

end
end CommonPhysicalRealization

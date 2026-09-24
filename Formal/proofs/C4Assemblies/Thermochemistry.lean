import proofs.C4Assemblies.LiteralSource
import proofs.C4Assemblies.Family

namespace C4Assemblies
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem transfer_element_balance (e : TransferLabel ι) (element : Fin 3) :
    (∑ i, ∑ s : Fin 6,
      (CommonPhysicalRealization.composition (s.castLE (by decide)) element : ℝ)*
        transferIncrement e i s) = 0 :=
  transfer_property_balance _ e

theorem transfer_potential_balance (e : TransferLabel ι) :
    (∑ i, ∑ s : Fin 6,
      CommonPhysicalRealization.standardPotential (s.castLE (by decide))*
        transferIncrement e i s) = 0 :=
  transfer_property_balance _ e

theorem transfer_thermochemistry (P : Parameters ι) (a b : ι) (s : Fin 6)
    (hab : 0 < P.k a b) :
    0 < P.k b a ∧ Real.log (P.k a b / P.k b a) =
      -(∑ i, ∑ l : Fin 6,
        CommonPhysicalRealization.standardPotential (l.castLE (by decide))*
          transferIncrement (a,b,s) i l) := by
  rw [← P.exchange_symmetric a b,transfer_potential_balance]
  simp [hab,ne_of_gt hab]

omit [Fintype ι] [DecidableEq ι] in
theorem node_common_thermochemistry (P : Parameters ι) (i : ι) (j : Fin 6) :
    0 < CommonPhysicalRealization.forwardCoefficient (P.r i) (P.d i) j ∧
    0 < CommonPhysicalRealization.reverseCoefficient (P.r i) (P.d i) j ∧
    Real.log (CommonPhysicalRealization.forwardCoefficient (P.r i) (P.d i) j /
      CommonPhysicalRealization.reverseCoefficient (P.r i) (P.d i) j) =
      ∑ s, ((CommonPhysicalRealization.pairLeft j s : ℝ)-
        CommonPhysicalRealization.pairRight j s)*CommonPhysicalRealization.standardPotential s :=
  CommonPhysicalRealization.common_thermochemistry (P.r i) (P.d i)
    (by linarith [P.r_lower i]) (by linarith [P.d_lower i]) j

end
end C4Assemblies

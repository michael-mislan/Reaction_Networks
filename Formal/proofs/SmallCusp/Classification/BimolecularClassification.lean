import proofs.SmallCusp.Classification.BimolecularClassificationCore
import proofs.SmallCusp.Classification.SourceCoverageLookup

namespace SmallCusp

theorem no_cusp_if_not_in_52 (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q)
    (hnot : ¬ BelongsToBimolecularCuspClass Q) : ¬ AdmitsTransverseCusp Q :=
  no_cusp_if_not_in_52_of_coverage structurallyEligibleSource_isCovered Q hQ hnot

/-- Literal planar bimolecular `(2,5,2)` cusp classification. -/
theorem classify_planar_bimolecular_2_5_2_cusps
    (Q : SmallPlanarNetwork 5) (hQ : IsPlanarBimolecular252 Q) :
    AdmitsTransverseCusp Q ↔ BelongsToBimolecularCuspClass Q :=
  classify_planar_bimolecular_2_5_2_cusps_of_coverage
    structurallyEligibleSource_isCovered Q hQ

end SmallCusp

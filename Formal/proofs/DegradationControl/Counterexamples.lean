import proofs.DegradationControl.Certificates

namespace DegradationControl

def reducibleGrowthMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![1, 0], ![0, -1]]

def reducibleCriticalMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![0, 0], ![0, -1]]

/-- A reducible matrix may have a positive eigenvalue in one block but no
strictly positive global subsolution. -/
theorem reducible_growth_has_no_strict_global_certificate :
    ¬ GrowthCertificate reducibleGrowthMatrix := by
  rintro ⟨v, hv, hMv⟩
  have hv1 : 0 < v 1 := hv 1
  have hm1 : 0 < Matrix.mulVec reducibleGrowthMatrix v 1 := hMv 1
  simp [reducibleGrowthMatrix, Matrix.mulVec] at hm1
  change v 1 < 0 at hm1
  linarith

/-- A reducible matrix may have spectral bound zero in one block but no
strictly positive global nullvector. -/
theorem reducible_critical_has_no_positive_nullvector :
    ¬ CriticalCertificate reducibleCriticalMatrix := by
  rintro ⟨v, hv, hMv⟩
  have hv1 : 0 < v 1 := hv 1
  have hm1 := congrFun hMv 1
  simp [reducibleCriticalMatrix, Matrix.mulVec] at hm1
  change v 1 = 0 at hm1
  linarith

end DegradationControl

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A1

namespace SmallCusp

def sourceCoverageTargetSlice59A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59A0 ++
  sourceCoverageTargetSlice59A1

theorem sourceCoverageTargetSlice59A_targetConsistent :
    sourceCoverageTargetSlice59A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59A,
    sourceCoverageTargetSlice59A0_targetConsistent,
    sourceCoverageTargetSlice59A1_targetConsistent]

theorem sourceCoverageTargetSlice59A_length : sourceCoverageTargetSlice59A.length = 250 := by
  simp [sourceCoverageTargetSlice59A,
    sourceCoverageTargetSlice59A0_length,
    sourceCoverageTargetSlice59A1_length]

end SmallCusp

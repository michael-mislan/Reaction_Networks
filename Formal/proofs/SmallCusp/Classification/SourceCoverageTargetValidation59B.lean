import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B1

namespace SmallCusp

def sourceCoverageTargetSlice59B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59B0 ++
  sourceCoverageTargetSlice59B1

theorem sourceCoverageTargetSlice59B_targetConsistent :
    sourceCoverageTargetSlice59B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59B,
    sourceCoverageTargetSlice59B0_targetConsistent,
    sourceCoverageTargetSlice59B1_targetConsistent]

theorem sourceCoverageTargetSlice59B_length : sourceCoverageTargetSlice59B.length = 250 := by
  simp [sourceCoverageTargetSlice59B,
    sourceCoverageTargetSlice59B0_length,
    sourceCoverageTargetSlice59B1_length]

end SmallCusp

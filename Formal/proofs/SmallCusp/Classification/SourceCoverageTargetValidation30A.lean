import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A1

namespace SmallCusp

def sourceCoverageTargetSlice30A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30A0 ++
  sourceCoverageTargetSlice30A1

theorem sourceCoverageTargetSlice30A_targetConsistent :
    sourceCoverageTargetSlice30A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30A,
    sourceCoverageTargetSlice30A0_targetConsistent,
    sourceCoverageTargetSlice30A1_targetConsistent]

theorem sourceCoverageTargetSlice30A_length : sourceCoverageTargetSlice30A.length = 250 := by
  simp [sourceCoverageTargetSlice30A,
    sourceCoverageTargetSlice30A0_length,
    sourceCoverageTargetSlice30A1_length]

end SmallCusp

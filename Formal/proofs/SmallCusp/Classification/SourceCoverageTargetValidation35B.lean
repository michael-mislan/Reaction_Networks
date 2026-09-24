import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B1

namespace SmallCusp

def sourceCoverageTargetSlice35B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35B0 ++
  sourceCoverageTargetSlice35B1

theorem sourceCoverageTargetSlice35B_targetConsistent :
    sourceCoverageTargetSlice35B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35B,
    sourceCoverageTargetSlice35B0_targetConsistent,
    sourceCoverageTargetSlice35B1_targetConsistent]

theorem sourceCoverageTargetSlice35B_length : sourceCoverageTargetSlice35B.length = 250 := by
  simp [sourceCoverageTargetSlice35B,
    sourceCoverageTargetSlice35B0_length,
    sourceCoverageTargetSlice35B1_length]

end SmallCusp

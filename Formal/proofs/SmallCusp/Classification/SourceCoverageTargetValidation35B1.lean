import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B11

namespace SmallCusp

def sourceCoverageTargetSlice35B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35B10 ++
  sourceCoverageTargetSlice35B11

theorem sourceCoverageTargetSlice35B1_targetConsistent :
    sourceCoverageTargetSlice35B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35B1,
    sourceCoverageTargetSlice35B10_targetConsistent,
    sourceCoverageTargetSlice35B11_targetConsistent]

theorem sourceCoverageTargetSlice35B1_length : sourceCoverageTargetSlice35B1.length = 125 := by
  simp [sourceCoverageTargetSlice35B1,
    sourceCoverageTargetSlice35B10_length,
    sourceCoverageTargetSlice35B11_length]

end SmallCusp

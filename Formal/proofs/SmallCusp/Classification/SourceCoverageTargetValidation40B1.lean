import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B11

namespace SmallCusp

def sourceCoverageTargetSlice40B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40B10 ++
  sourceCoverageTargetSlice40B11

theorem sourceCoverageTargetSlice40B1_targetConsistent :
    sourceCoverageTargetSlice40B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40B1,
    sourceCoverageTargetSlice40B10_targetConsistent,
    sourceCoverageTargetSlice40B11_targetConsistent]

theorem sourceCoverageTargetSlice40B1_length : sourceCoverageTargetSlice40B1.length = 125 := by
  simp [sourceCoverageTargetSlice40B1,
    sourceCoverageTargetSlice40B10_length,
    sourceCoverageTargetSlice40B11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B11

namespace SmallCusp

def sourceCoverageTargetSlice39B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39B10 ++
  sourceCoverageTargetSlice39B11

theorem sourceCoverageTargetSlice39B1_targetConsistent :
    sourceCoverageTargetSlice39B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39B1,
    sourceCoverageTargetSlice39B10_targetConsistent,
    sourceCoverageTargetSlice39B11_targetConsistent]

theorem sourceCoverageTargetSlice39B1_length : sourceCoverageTargetSlice39B1.length = 125 := by
  simp [sourceCoverageTargetSlice39B1,
    sourceCoverageTargetSlice39B10_length,
    sourceCoverageTargetSlice39B11_length]

end SmallCusp

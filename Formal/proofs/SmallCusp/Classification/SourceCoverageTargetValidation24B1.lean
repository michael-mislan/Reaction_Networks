import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B11

namespace SmallCusp

def sourceCoverageTargetSlice24B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24B10 ++
  sourceCoverageTargetSlice24B11

theorem sourceCoverageTargetSlice24B1_targetConsistent :
    sourceCoverageTargetSlice24B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24B1,
    sourceCoverageTargetSlice24B10_targetConsistent,
    sourceCoverageTargetSlice24B11_targetConsistent]

theorem sourceCoverageTargetSlice24B1_length : sourceCoverageTargetSlice24B1.length = 125 := by
  simp [sourceCoverageTargetSlice24B1,
    sourceCoverageTargetSlice24B10_length,
    sourceCoverageTargetSlice24B11_length]

end SmallCusp

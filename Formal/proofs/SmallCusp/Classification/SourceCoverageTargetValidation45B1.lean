import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B11

namespace SmallCusp

def sourceCoverageTargetSlice45B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45B10 ++
  sourceCoverageTargetSlice45B11

theorem sourceCoverageTargetSlice45B1_targetConsistent :
    sourceCoverageTargetSlice45B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45B1,
    sourceCoverageTargetSlice45B10_targetConsistent,
    sourceCoverageTargetSlice45B11_targetConsistent]

theorem sourceCoverageTargetSlice45B1_length : sourceCoverageTargetSlice45B1.length = 125 := by
  simp [sourceCoverageTargetSlice45B1,
    sourceCoverageTargetSlice45B10_length,
    sourceCoverageTargetSlice45B11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B01

namespace SmallCusp

def sourceCoverageTargetSlice22B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22B00 ++
  sourceCoverageTargetSlice22B01

theorem sourceCoverageTargetSlice22B0_targetConsistent :
    sourceCoverageTargetSlice22B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22B0,
    sourceCoverageTargetSlice22B00_targetConsistent,
    sourceCoverageTargetSlice22B01_targetConsistent]

theorem sourceCoverageTargetSlice22B0_length : sourceCoverageTargetSlice22B0.length = 125 := by
  simp [sourceCoverageTargetSlice22B0,
    sourceCoverageTargetSlice22B00_length,
    sourceCoverageTargetSlice22B01_length]

end SmallCusp

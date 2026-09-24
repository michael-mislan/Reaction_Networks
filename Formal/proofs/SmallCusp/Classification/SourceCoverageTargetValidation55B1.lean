import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B11

namespace SmallCusp

def sourceCoverageTargetSlice55B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55B10 ++
  sourceCoverageTargetSlice55B11

theorem sourceCoverageTargetSlice55B1_targetConsistent :
    sourceCoverageTargetSlice55B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55B1,
    sourceCoverageTargetSlice55B10_targetConsistent,
    sourceCoverageTargetSlice55B11_targetConsistent]

theorem sourceCoverageTargetSlice55B1_length : sourceCoverageTargetSlice55B1.length = 125 := by
  simp [sourceCoverageTargetSlice55B1,
    sourceCoverageTargetSlice55B10_length,
    sourceCoverageTargetSlice55B11_length]

end SmallCusp

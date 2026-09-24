import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B01

namespace SmallCusp

def sourceCoverageTargetSlice55B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55B00 ++
  sourceCoverageTargetSlice55B01

theorem sourceCoverageTargetSlice55B0_targetConsistent :
    sourceCoverageTargetSlice55B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55B0,
    sourceCoverageTargetSlice55B00_targetConsistent,
    sourceCoverageTargetSlice55B01_targetConsistent]

theorem sourceCoverageTargetSlice55B0_length : sourceCoverageTargetSlice55B0.length = 125 := by
  simp [sourceCoverageTargetSlice55B0,
    sourceCoverageTargetSlice55B00_length,
    sourceCoverageTargetSlice55B01_length]

end SmallCusp

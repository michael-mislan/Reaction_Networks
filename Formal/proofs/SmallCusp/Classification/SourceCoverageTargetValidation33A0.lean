import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A01

namespace SmallCusp

def sourceCoverageTargetSlice33A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33A00 ++
  sourceCoverageTargetSlice33A01

theorem sourceCoverageTargetSlice33A0_targetConsistent :
    sourceCoverageTargetSlice33A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33A0,
    sourceCoverageTargetSlice33A00_targetConsistent,
    sourceCoverageTargetSlice33A01_targetConsistent]

theorem sourceCoverageTargetSlice33A0_length : sourceCoverageTargetSlice33A0.length = 125 := by
  simp [sourceCoverageTargetSlice33A0,
    sourceCoverageTargetSlice33A00_length,
    sourceCoverageTargetSlice33A01_length]

end SmallCusp

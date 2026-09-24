import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A01

namespace SmallCusp

def sourceCoverageTargetSlice55A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55A00 ++
  sourceCoverageTargetSlice55A01

theorem sourceCoverageTargetSlice55A0_targetConsistent :
    sourceCoverageTargetSlice55A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55A0,
    sourceCoverageTargetSlice55A00_targetConsistent,
    sourceCoverageTargetSlice55A01_targetConsistent]

theorem sourceCoverageTargetSlice55A0_length : sourceCoverageTargetSlice55A0.length = 125 := by
  simp [sourceCoverageTargetSlice55A0,
    sourceCoverageTargetSlice55A00_length,
    sourceCoverageTargetSlice55A01_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A01

namespace SmallCusp

def sourceCoverageTargetSlice54A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54A00 ++
  sourceCoverageTargetSlice54A01

theorem sourceCoverageTargetSlice54A0_targetConsistent :
    sourceCoverageTargetSlice54A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54A0,
    sourceCoverageTargetSlice54A00_targetConsistent,
    sourceCoverageTargetSlice54A01_targetConsistent]

theorem sourceCoverageTargetSlice54A0_length : sourceCoverageTargetSlice54A0.length = 125 := by
  simp [sourceCoverageTargetSlice54A0,
    sourceCoverageTargetSlice54A00_length,
    sourceCoverageTargetSlice54A01_length]

end SmallCusp

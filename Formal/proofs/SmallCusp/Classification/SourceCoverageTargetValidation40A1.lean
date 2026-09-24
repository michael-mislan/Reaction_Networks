import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A11

namespace SmallCusp

def sourceCoverageTargetSlice40A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40A10 ++
  sourceCoverageTargetSlice40A11

theorem sourceCoverageTargetSlice40A1_targetConsistent :
    sourceCoverageTargetSlice40A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40A1,
    sourceCoverageTargetSlice40A10_targetConsistent,
    sourceCoverageTargetSlice40A11_targetConsistent]

theorem sourceCoverageTargetSlice40A1_length : sourceCoverageTargetSlice40A1.length = 125 := by
  simp [sourceCoverageTargetSlice40A1,
    sourceCoverageTargetSlice40A10_length,
    sourceCoverageTargetSlice40A11_length]

end SmallCusp

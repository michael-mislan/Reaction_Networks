import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A11

namespace SmallCusp

def sourceCoverageTargetSlice15A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15A10 ++
  sourceCoverageTargetSlice15A11

theorem sourceCoverageTargetSlice15A1_targetConsistent :
    sourceCoverageTargetSlice15A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15A1,
    sourceCoverageTargetSlice15A10_targetConsistent,
    sourceCoverageTargetSlice15A11_targetConsistent]

theorem sourceCoverageTargetSlice15A1_length : sourceCoverageTargetSlice15A1.length = 125 := by
  simp [sourceCoverageTargetSlice15A1,
    sourceCoverageTargetSlice15A10_length,
    sourceCoverageTargetSlice15A11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A1

namespace SmallCusp

def sourceCoverageTargetSlice15A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15A0 ++
  sourceCoverageTargetSlice15A1

theorem sourceCoverageTargetSlice15A_targetConsistent :
    sourceCoverageTargetSlice15A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15A,
    sourceCoverageTargetSlice15A0_targetConsistent,
    sourceCoverageTargetSlice15A1_targetConsistent]

theorem sourceCoverageTargetSlice15A_length : sourceCoverageTargetSlice15A.length = 250 := by
  simp [sourceCoverageTargetSlice15A,
    sourceCoverageTargetSlice15A0_length,
    sourceCoverageTargetSlice15A1_length]

end SmallCusp

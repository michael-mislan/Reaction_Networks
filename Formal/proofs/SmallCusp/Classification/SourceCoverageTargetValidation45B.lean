import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B1

namespace SmallCusp

def sourceCoverageTargetSlice45B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45B0 ++
  sourceCoverageTargetSlice45B1

theorem sourceCoverageTargetSlice45B_targetConsistent :
    sourceCoverageTargetSlice45B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45B,
    sourceCoverageTargetSlice45B0_targetConsistent,
    sourceCoverageTargetSlice45B1_targetConsistent]

theorem sourceCoverageTargetSlice45B_length : sourceCoverageTargetSlice45B.length = 250 := by
  simp [sourceCoverageTargetSlice45B,
    sourceCoverageTargetSlice45B0_length,
    sourceCoverageTargetSlice45B1_length]

end SmallCusp

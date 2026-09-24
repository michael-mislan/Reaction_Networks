import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B1

namespace SmallCusp

def sourceCoverageTargetSlice55B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55B0 ++
  sourceCoverageTargetSlice55B1

theorem sourceCoverageTargetSlice55B_targetConsistent :
    sourceCoverageTargetSlice55B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55B,
    sourceCoverageTargetSlice55B0_targetConsistent,
    sourceCoverageTargetSlice55B1_targetConsistent]

theorem sourceCoverageTargetSlice55B_length : sourceCoverageTargetSlice55B.length = 250 := by
  simp [sourceCoverageTargetSlice55B,
    sourceCoverageTargetSlice55B0_length,
    sourceCoverageTargetSlice55B1_length]

end SmallCusp

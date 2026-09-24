import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B1

namespace SmallCusp

def sourceCoverageTargetSlice17B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17B0 ++
  sourceCoverageTargetSlice17B1

theorem sourceCoverageTargetSlice17B_targetConsistent :
    sourceCoverageTargetSlice17B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17B,
    sourceCoverageTargetSlice17B0_targetConsistent,
    sourceCoverageTargetSlice17B1_targetConsistent]

theorem sourceCoverageTargetSlice17B_length : sourceCoverageTargetSlice17B.length = 250 := by
  simp [sourceCoverageTargetSlice17B,
    sourceCoverageTargetSlice17B0_length,
    sourceCoverageTargetSlice17B1_length]

end SmallCusp

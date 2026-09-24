import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B11

namespace SmallCusp

def sourceCoverageTargetSlice17B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17B10 ++
  sourceCoverageTargetSlice17B11

theorem sourceCoverageTargetSlice17B1_targetConsistent :
    sourceCoverageTargetSlice17B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17B1,
    sourceCoverageTargetSlice17B10_targetConsistent,
    sourceCoverageTargetSlice17B11_targetConsistent]

theorem sourceCoverageTargetSlice17B1_length : sourceCoverageTargetSlice17B1.length = 125 := by
  simp [sourceCoverageTargetSlice17B1,
    sourceCoverageTargetSlice17B10_length,
    sourceCoverageTargetSlice17B11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B01

namespace SmallCusp

def sourceCoverageTargetSlice17B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17B00 ++
  sourceCoverageTargetSlice17B01

theorem sourceCoverageTargetSlice17B0_targetConsistent :
    sourceCoverageTargetSlice17B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17B0,
    sourceCoverageTargetSlice17B00_targetConsistent,
    sourceCoverageTargetSlice17B01_targetConsistent]

theorem sourceCoverageTargetSlice17B0_length : sourceCoverageTargetSlice17B0.length = 125 := by
  simp [sourceCoverageTargetSlice17B0,
    sourceCoverageTargetSlice17B00_length,
    sourceCoverageTargetSlice17B01_length]

end SmallCusp

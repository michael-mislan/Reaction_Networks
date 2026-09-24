import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B1

namespace SmallCusp

def sourceCoverageTargetSlice25B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25B0 ++
  sourceCoverageTargetSlice25B1

theorem sourceCoverageTargetSlice25B_targetConsistent :
    sourceCoverageTargetSlice25B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25B,
    sourceCoverageTargetSlice25B0_targetConsistent,
    sourceCoverageTargetSlice25B1_targetConsistent]

theorem sourceCoverageTargetSlice25B_length : sourceCoverageTargetSlice25B.length = 250 := by
  simp [sourceCoverageTargetSlice25B,
    sourceCoverageTargetSlice25B0_length,
    sourceCoverageTargetSlice25B1_length]

end SmallCusp

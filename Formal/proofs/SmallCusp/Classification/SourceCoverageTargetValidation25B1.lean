import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B11

namespace SmallCusp

def sourceCoverageTargetSlice25B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25B10 ++
  sourceCoverageTargetSlice25B11

theorem sourceCoverageTargetSlice25B1_targetConsistent :
    sourceCoverageTargetSlice25B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25B1,
    sourceCoverageTargetSlice25B10_targetConsistent,
    sourceCoverageTargetSlice25B11_targetConsistent]

theorem sourceCoverageTargetSlice25B1_length : sourceCoverageTargetSlice25B1.length = 125 := by
  simp [sourceCoverageTargetSlice25B1,
    sourceCoverageTargetSlice25B10_length,
    sourceCoverageTargetSlice25B11_length]

end SmallCusp

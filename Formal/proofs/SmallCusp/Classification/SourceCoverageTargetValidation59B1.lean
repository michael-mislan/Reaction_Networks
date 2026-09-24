import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B11

namespace SmallCusp

def sourceCoverageTargetSlice59B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59B10 ++
  sourceCoverageTargetSlice59B11

theorem sourceCoverageTargetSlice59B1_targetConsistent :
    sourceCoverageTargetSlice59B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59B1,
    sourceCoverageTargetSlice59B10_targetConsistent,
    sourceCoverageTargetSlice59B11_targetConsistent]

theorem sourceCoverageTargetSlice59B1_length : sourceCoverageTargetSlice59B1.length = 125 := by
  simp [sourceCoverageTargetSlice59B1,
    sourceCoverageTargetSlice59B10_length,
    sourceCoverageTargetSlice59B11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B11

namespace SmallCusp

def sourceCoverageTargetSlice58B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58B10 ++
  sourceCoverageTargetSlice58B11

theorem sourceCoverageTargetSlice58B1_targetConsistent :
    sourceCoverageTargetSlice58B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58B1,
    sourceCoverageTargetSlice58B10_targetConsistent,
    sourceCoverageTargetSlice58B11_targetConsistent]

theorem sourceCoverageTargetSlice58B1_length : sourceCoverageTargetSlice58B1.length = 125 := by
  simp [sourceCoverageTargetSlice58B1,
    sourceCoverageTargetSlice58B10_length,
    sourceCoverageTargetSlice58B11_length]

end SmallCusp

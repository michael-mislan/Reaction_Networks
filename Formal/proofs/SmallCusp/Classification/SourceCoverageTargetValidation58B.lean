import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B1

namespace SmallCusp

def sourceCoverageTargetSlice58B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58B0 ++
  sourceCoverageTargetSlice58B1

theorem sourceCoverageTargetSlice58B_targetConsistent :
    sourceCoverageTargetSlice58B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58B,
    sourceCoverageTargetSlice58B0_targetConsistent,
    sourceCoverageTargetSlice58B1_targetConsistent]

theorem sourceCoverageTargetSlice58B_length : sourceCoverageTargetSlice58B.length = 250 := by
  simp [sourceCoverageTargetSlice58B,
    sourceCoverageTargetSlice58B0_length,
    sourceCoverageTargetSlice58B1_length]

end SmallCusp

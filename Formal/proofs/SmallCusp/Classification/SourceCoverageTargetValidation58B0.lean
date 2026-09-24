import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58B01

namespace SmallCusp

def sourceCoverageTargetSlice58B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58B00 ++
  sourceCoverageTargetSlice58B01

theorem sourceCoverageTargetSlice58B0_targetConsistent :
    sourceCoverageTargetSlice58B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58B0,
    sourceCoverageTargetSlice58B00_targetConsistent,
    sourceCoverageTargetSlice58B01_targetConsistent]

theorem sourceCoverageTargetSlice58B0_length : sourceCoverageTargetSlice58B0.length = 125 := by
  simp [sourceCoverageTargetSlice58B0,
    sourceCoverageTargetSlice58B00_length,
    sourceCoverageTargetSlice58B01_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B01

namespace SmallCusp

def sourceCoverageTargetSlice20B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20B00 ++
  sourceCoverageTargetSlice20B01

theorem sourceCoverageTargetSlice20B0_targetConsistent :
    sourceCoverageTargetSlice20B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20B0,
    sourceCoverageTargetSlice20B00_targetConsistent,
    sourceCoverageTargetSlice20B01_targetConsistent]

theorem sourceCoverageTargetSlice20B0_length : sourceCoverageTargetSlice20B0.length = 125 := by
  simp [sourceCoverageTargetSlice20B0,
    sourceCoverageTargetSlice20B00_length,
    sourceCoverageTargetSlice20B01_length]

end SmallCusp

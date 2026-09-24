import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B11

namespace SmallCusp

def sourceCoverageTargetSlice20B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20B10 ++
  sourceCoverageTargetSlice20B11

theorem sourceCoverageTargetSlice20B1_targetConsistent :
    sourceCoverageTargetSlice20B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20B1,
    sourceCoverageTargetSlice20B10_targetConsistent,
    sourceCoverageTargetSlice20B11_targetConsistent]

theorem sourceCoverageTargetSlice20B1_length : sourceCoverageTargetSlice20B1.length = 125 := by
  simp [sourceCoverageTargetSlice20B1,
    sourceCoverageTargetSlice20B10_length,
    sourceCoverageTargetSlice20B11_length]

end SmallCusp

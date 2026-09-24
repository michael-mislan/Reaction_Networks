import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B1

namespace SmallCusp

def sourceCoverageTargetSlice20B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20B0 ++
  sourceCoverageTargetSlice20B1

theorem sourceCoverageTargetSlice20B_targetConsistent :
    sourceCoverageTargetSlice20B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20B,
    sourceCoverageTargetSlice20B0_targetConsistent,
    sourceCoverageTargetSlice20B1_targetConsistent]

theorem sourceCoverageTargetSlice20B_length : sourceCoverageTargetSlice20B.length = 250 := by
  simp [sourceCoverageTargetSlice20B,
    sourceCoverageTargetSlice20B0_length,
    sourceCoverageTargetSlice20B1_length]

end SmallCusp

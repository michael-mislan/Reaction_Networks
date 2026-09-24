import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A11

namespace SmallCusp

def sourceCoverageTargetSlice20A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20A10 ++
  sourceCoverageTargetSlice20A11

theorem sourceCoverageTargetSlice20A1_targetConsistent :
    sourceCoverageTargetSlice20A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20A1,
    sourceCoverageTargetSlice20A10_targetConsistent,
    sourceCoverageTargetSlice20A11_targetConsistent]

theorem sourceCoverageTargetSlice20A1_length : sourceCoverageTargetSlice20A1.length = 125 := by
  simp [sourceCoverageTargetSlice20A1,
    sourceCoverageTargetSlice20A10_length,
    sourceCoverageTargetSlice20A11_length]

end SmallCusp

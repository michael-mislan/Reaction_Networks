import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A1

namespace SmallCusp

def sourceCoverageTargetSlice20A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20A0 ++
  sourceCoverageTargetSlice20A1

theorem sourceCoverageTargetSlice20A_targetConsistent :
    sourceCoverageTargetSlice20A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20A,
    sourceCoverageTargetSlice20A0_targetConsistent,
    sourceCoverageTargetSlice20A1_targetConsistent]

theorem sourceCoverageTargetSlice20A_length : sourceCoverageTargetSlice20A.length = 250 := by
  simp [sourceCoverageTargetSlice20A,
    sourceCoverageTargetSlice20A0_length,
    sourceCoverageTargetSlice20A1_length]

end SmallCusp

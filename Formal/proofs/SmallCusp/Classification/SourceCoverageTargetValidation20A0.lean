import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A01

namespace SmallCusp

def sourceCoverageTargetSlice20A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice20A00 ++
  sourceCoverageTargetSlice20A01

theorem sourceCoverageTargetSlice20A0_targetConsistent :
    sourceCoverageTargetSlice20A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice20A0,
    sourceCoverageTargetSlice20A00_targetConsistent,
    sourceCoverageTargetSlice20A01_targetConsistent]

theorem sourceCoverageTargetSlice20A0_length : sourceCoverageTargetSlice20A0.length = 125 := by
  simp [sourceCoverageTargetSlice20A0,
    sourceCoverageTargetSlice20A00_length,
    sourceCoverageTargetSlice20A01_length]

end SmallCusp

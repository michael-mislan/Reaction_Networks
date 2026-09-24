import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A01

namespace SmallCusp

def sourceCoverageTargetSlice30A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30A00 ++
  sourceCoverageTargetSlice30A01

theorem sourceCoverageTargetSlice30A0_targetConsistent :
    sourceCoverageTargetSlice30A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30A0,
    sourceCoverageTargetSlice30A00_targetConsistent,
    sourceCoverageTargetSlice30A01_targetConsistent]

theorem sourceCoverageTargetSlice30A0_length : sourceCoverageTargetSlice30A0.length = 125 := by
  simp [sourceCoverageTargetSlice30A0,
    sourceCoverageTargetSlice30A00_length,
    sourceCoverageTargetSlice30A01_length]

end SmallCusp

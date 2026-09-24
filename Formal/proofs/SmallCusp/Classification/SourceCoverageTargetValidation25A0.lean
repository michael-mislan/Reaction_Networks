import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A01

namespace SmallCusp

def sourceCoverageTargetSlice25A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25A00 ++
  sourceCoverageTargetSlice25A01

theorem sourceCoverageTargetSlice25A0_targetConsistent :
    sourceCoverageTargetSlice25A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25A0,
    sourceCoverageTargetSlice25A00_targetConsistent,
    sourceCoverageTargetSlice25A01_targetConsistent]

theorem sourceCoverageTargetSlice25A0_length : sourceCoverageTargetSlice25A0.length = 125 := by
  simp [sourceCoverageTargetSlice25A0,
    sourceCoverageTargetSlice25A00_length,
    sourceCoverageTargetSlice25A01_length]

end SmallCusp

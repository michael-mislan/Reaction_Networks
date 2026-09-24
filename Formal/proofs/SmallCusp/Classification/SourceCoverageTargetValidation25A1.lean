import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A11

namespace SmallCusp

def sourceCoverageTargetSlice25A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25A10 ++
  sourceCoverageTargetSlice25A11

theorem sourceCoverageTargetSlice25A1_targetConsistent :
    sourceCoverageTargetSlice25A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25A1,
    sourceCoverageTargetSlice25A10_targetConsistent,
    sourceCoverageTargetSlice25A11_targetConsistent]

theorem sourceCoverageTargetSlice25A1_length : sourceCoverageTargetSlice25A1.length = 125 := by
  simp [sourceCoverageTargetSlice25A1,
    sourceCoverageTargetSlice25A10_length,
    sourceCoverageTargetSlice25A11_length]

end SmallCusp

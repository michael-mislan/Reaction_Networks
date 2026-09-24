import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A11

namespace SmallCusp

def sourceCoverageTargetSlice59A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59A10 ++
  sourceCoverageTargetSlice59A11

theorem sourceCoverageTargetSlice59A1_targetConsistent :
    sourceCoverageTargetSlice59A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59A1,
    sourceCoverageTargetSlice59A10_targetConsistent,
    sourceCoverageTargetSlice59A11_targetConsistent]

theorem sourceCoverageTargetSlice59A1_length : sourceCoverageTargetSlice59A1.length = 125 := by
  simp [sourceCoverageTargetSlice59A1,
    sourceCoverageTargetSlice59A10_length,
    sourceCoverageTargetSlice59A11_length]

end SmallCusp

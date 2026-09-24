import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A1

namespace SmallCusp

def sourceCoverageTargetSlice25A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25A0 ++
  sourceCoverageTargetSlice25A1

theorem sourceCoverageTargetSlice25A_targetConsistent :
    sourceCoverageTargetSlice25A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25A,
    sourceCoverageTargetSlice25A0_targetConsistent,
    sourceCoverageTargetSlice25A1_targetConsistent]

theorem sourceCoverageTargetSlice25A_length : sourceCoverageTargetSlice25A.length = 250 := by
  simp [sourceCoverageTargetSlice25A,
    sourceCoverageTargetSlice25A0_length,
    sourceCoverageTargetSlice25A1_length]

end SmallCusp

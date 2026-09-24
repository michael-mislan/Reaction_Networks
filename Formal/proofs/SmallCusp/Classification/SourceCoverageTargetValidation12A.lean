import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12A1

namespace SmallCusp

def sourceCoverageTargetSlice12A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice12A0 ++
  sourceCoverageTargetSlice12A1

theorem sourceCoverageTargetSlice12A_targetConsistent :
    sourceCoverageTargetSlice12A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice12A,
    sourceCoverageTargetSlice12A0_targetConsistent,
    sourceCoverageTargetSlice12A1_targetConsistent]

theorem sourceCoverageTargetSlice12A_length : sourceCoverageTargetSlice12A.length = 250 := by
  simp [sourceCoverageTargetSlice12A,
    sourceCoverageTargetSlice12A0_length,
    sourceCoverageTargetSlice12A1_length]

end SmallCusp

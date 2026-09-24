import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A1

namespace SmallCusp

def sourceCoverageTargetSlice38A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38A0 ++
  sourceCoverageTargetSlice38A1

theorem sourceCoverageTargetSlice38A_targetConsistent :
    sourceCoverageTargetSlice38A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38A,
    sourceCoverageTargetSlice38A0_targetConsistent,
    sourceCoverageTargetSlice38A1_targetConsistent]

theorem sourceCoverageTargetSlice38A_length : sourceCoverageTargetSlice38A.length = 250 := by
  simp [sourceCoverageTargetSlice38A,
    sourceCoverageTargetSlice38A0_length,
    sourceCoverageTargetSlice38A1_length]

end SmallCusp

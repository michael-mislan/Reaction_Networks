import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A11

namespace SmallCusp

def sourceCoverageTargetSlice38A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38A10 ++
  sourceCoverageTargetSlice38A11

theorem sourceCoverageTargetSlice38A1_targetConsistent :
    sourceCoverageTargetSlice38A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38A1,
    sourceCoverageTargetSlice38A10_targetConsistent,
    sourceCoverageTargetSlice38A11_targetConsistent]

theorem sourceCoverageTargetSlice38A1_length : sourceCoverageTargetSlice38A1.length = 125 := by
  simp [sourceCoverageTargetSlice38A1,
    sourceCoverageTargetSlice38A10_length,
    sourceCoverageTargetSlice38A11_length]

end SmallCusp

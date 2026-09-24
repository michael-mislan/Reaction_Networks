import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B1

namespace SmallCusp

def sourceCoverageTargetSlice38B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38B0 ++
  sourceCoverageTargetSlice38B1

theorem sourceCoverageTargetSlice38B_targetConsistent :
    sourceCoverageTargetSlice38B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38B,
    sourceCoverageTargetSlice38B0_targetConsistent,
    sourceCoverageTargetSlice38B1_targetConsistent]

theorem sourceCoverageTargetSlice38B_length : sourceCoverageTargetSlice38B.length = 250 := by
  simp [sourceCoverageTargetSlice38B,
    sourceCoverageTargetSlice38B0_length,
    sourceCoverageTargetSlice38B1_length]

end SmallCusp

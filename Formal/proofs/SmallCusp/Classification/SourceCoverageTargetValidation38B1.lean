import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B11

namespace SmallCusp

def sourceCoverageTargetSlice38B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38B10 ++
  sourceCoverageTargetSlice38B11

theorem sourceCoverageTargetSlice38B1_targetConsistent :
    sourceCoverageTargetSlice38B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38B1,
    sourceCoverageTargetSlice38B10_targetConsistent,
    sourceCoverageTargetSlice38B11_targetConsistent]

theorem sourceCoverageTargetSlice38B1_length : sourceCoverageTargetSlice38B1.length = 125 := by
  simp [sourceCoverageTargetSlice38B1,
    sourceCoverageTargetSlice38B10_length,
    sourceCoverageTargetSlice38B11_length]

end SmallCusp

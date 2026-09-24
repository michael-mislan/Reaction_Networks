import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B01

namespace SmallCusp

def sourceCoverageTargetSlice38B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38B00 ++
  sourceCoverageTargetSlice38B01

theorem sourceCoverageTargetSlice38B0_targetConsistent :
    sourceCoverageTargetSlice38B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38B0,
    sourceCoverageTargetSlice38B00_targetConsistent,
    sourceCoverageTargetSlice38B01_targetConsistent]

theorem sourceCoverageTargetSlice38B0_length : sourceCoverageTargetSlice38B0.length = 125 := by
  simp [sourceCoverageTargetSlice38B0,
    sourceCoverageTargetSlice38B00_length,
    sourceCoverageTargetSlice38B01_length]

end SmallCusp

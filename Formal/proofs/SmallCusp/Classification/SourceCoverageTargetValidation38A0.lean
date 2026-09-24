import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A01

namespace SmallCusp

def sourceCoverageTargetSlice38A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice38A00 ++
  sourceCoverageTargetSlice38A01

theorem sourceCoverageTargetSlice38A0_targetConsistent :
    sourceCoverageTargetSlice38A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice38A0,
    sourceCoverageTargetSlice38A00_targetConsistent,
    sourceCoverageTargetSlice38A01_targetConsistent]

theorem sourceCoverageTargetSlice38A0_length : sourceCoverageTargetSlice38A0.length = 125 := by
  simp [sourceCoverageTargetSlice38A0,
    sourceCoverageTargetSlice38A00_length,
    sourceCoverageTargetSlice38A01_length]

end SmallCusp

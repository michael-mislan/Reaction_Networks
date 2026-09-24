import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation38B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch38_eq_targetSlices :
    sourceCoverageBatch38 = sourceCoverageTargetSlice38A ++
      sourceCoverageTargetSlice38B := by
  rfl

theorem sourceCoverageBatch38_targetConsistent :
    sourceCoverageBatch38.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch38_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice38A_targetConsistent,
    sourceCoverageTargetSlice38B_targetConsistent]
theorem sourceCoverageBatch38_length :
    sourceCoverageBatch38.length = 500 := by
  rw [sourceCoverageBatch38_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice38A_length,
    sourceCoverageTargetSlice38B_length]

end SmallCusp

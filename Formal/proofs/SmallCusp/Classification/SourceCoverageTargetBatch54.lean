import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch54_eq_targetSlices :
    sourceCoverageBatch54 = sourceCoverageTargetSlice54A ++
      sourceCoverageTargetSlice54B := by
  rfl

theorem sourceCoverageBatch54_targetConsistent :
    sourceCoverageBatch54.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch54_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice54A_targetConsistent,
    sourceCoverageTargetSlice54B_targetConsistent]
theorem sourceCoverageBatch54_length :
    sourceCoverageBatch54.length = 500 := by
  rw [sourceCoverageBatch54_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice54A_length,
    sourceCoverageTargetSlice54B_length]

end SmallCusp

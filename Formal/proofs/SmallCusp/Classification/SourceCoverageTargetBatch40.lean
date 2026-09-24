import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch40_eq_targetSlices :
    sourceCoverageBatch40 = sourceCoverageTargetSlice40A ++
      sourceCoverageTargetSlice40B := by
  rfl

theorem sourceCoverageBatch40_targetConsistent :
    sourceCoverageBatch40.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch40_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice40A_targetConsistent,
    sourceCoverageTargetSlice40B_targetConsistent]
theorem sourceCoverageBatch40_length :
    sourceCoverageBatch40.length = 500 := by
  rw [sourceCoverageBatch40_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice40A_length,
    sourceCoverageTargetSlice40B_length]

end SmallCusp

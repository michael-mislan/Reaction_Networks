import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch42_eq_targetSlices :
    sourceCoverageBatch42 = sourceCoverageTargetSlice42A ++
      sourceCoverageTargetSlice42B := by
  rfl

theorem sourceCoverageBatch42_targetConsistent :
    sourceCoverageBatch42.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch42_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice42A_targetConsistent,
    sourceCoverageTargetSlice42B_targetConsistent]
theorem sourceCoverageBatch42_length :
    sourceCoverageBatch42.length = 500 := by
  rw [sourceCoverageBatch42_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice42A_length,
    sourceCoverageTargetSlice42B_length]

end SmallCusp

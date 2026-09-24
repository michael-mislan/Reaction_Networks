import proofs.SmallCusp.Classification.SourceCoverageTargetValidation00A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation00B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch00_eq_targetSlices :
    sourceCoverageBatch00 = sourceCoverageTargetSlice00A ++
      sourceCoverageTargetSlice00B := by
  rfl

theorem sourceCoverageBatch00_targetConsistent :
    sourceCoverageBatch00.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch00_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice00A_targetConsistent,
    sourceCoverageTargetSlice00B_targetConsistent]
theorem sourceCoverageBatch00_length :
    sourceCoverageBatch00.length = 500 := by
  rw [sourceCoverageBatch00_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice00A_length,
    sourceCoverageTargetSlice00B_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch12_eq_targetSlices :
    sourceCoverageBatch12 = sourceCoverageTargetSlice12A ++
      sourceCoverageTargetSlice12B := by
  rfl

theorem sourceCoverageBatch12_targetConsistent :
    sourceCoverageBatch12.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch12_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice12A_targetConsistent,
    sourceCoverageTargetSlice12B_targetConsistent]
theorem sourceCoverageBatch12_length :
    sourceCoverageBatch12.length = 500 := by
  rw [sourceCoverageBatch12_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice12A_length,
    sourceCoverageTargetSlice12B_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation04A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation04B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch04_eq_targetSlices :
    sourceCoverageBatch04 = sourceCoverageTargetSlice04A ++
      sourceCoverageTargetSlice04B := by
  rfl

theorem sourceCoverageBatch04_targetConsistent :
    sourceCoverageBatch04.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch04_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice04A_targetConsistent,
    sourceCoverageTargetSlice04B_targetConsistent]
theorem sourceCoverageBatch04_length :
    sourceCoverageBatch04.length = 500 := by
  rw [sourceCoverageBatch04_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice04A_length,
    sourceCoverageTargetSlice04B_length]

end SmallCusp

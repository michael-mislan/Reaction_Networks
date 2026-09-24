import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch25_eq_targetSlices :
    sourceCoverageBatch25 = sourceCoverageTargetSlice25A ++
      sourceCoverageTargetSlice25B := by
  rfl

theorem sourceCoverageBatch25_targetConsistent :
    sourceCoverageBatch25.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch25_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice25A_targetConsistent,
    sourceCoverageTargetSlice25B_targetConsistent]
theorem sourceCoverageBatch25_length :
    sourceCoverageBatch25.length = 500 := by
  rw [sourceCoverageBatch25_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice25A_length,
    sourceCoverageTargetSlice25B_length]

end SmallCusp

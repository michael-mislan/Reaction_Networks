import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch33_eq_targetSlices :
    sourceCoverageBatch33 = sourceCoverageTargetSlice33A ++
      sourceCoverageTargetSlice33B := by
  rfl

theorem sourceCoverageBatch33_targetConsistent :
    sourceCoverageBatch33.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch33_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice33A_targetConsistent,
    sourceCoverageTargetSlice33B_targetConsistent]
theorem sourceCoverageBatch33_length :
    sourceCoverageBatch33.length = 500 := by
  rw [sourceCoverageBatch33_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice33A_length,
    sourceCoverageTargetSlice33B_length]

end SmallCusp

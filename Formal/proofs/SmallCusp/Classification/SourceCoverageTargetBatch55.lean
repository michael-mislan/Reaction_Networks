import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch55_eq_targetSlices :
    sourceCoverageBatch55 = sourceCoverageTargetSlice55A ++
      sourceCoverageTargetSlice55B := by
  rfl

theorem sourceCoverageBatch55_targetConsistent :
    sourceCoverageBatch55.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch55_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice55A_targetConsistent,
    sourceCoverageTargetSlice55B_targetConsistent]
theorem sourceCoverageBatch55_length :
    sourceCoverageBatch55.length = 500 := by
  rw [sourceCoverageBatch55_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice55A_length,
    sourceCoverageTargetSlice55B_length]

end SmallCusp

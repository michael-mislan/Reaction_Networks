import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation20B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch20_eq_targetSlices :
    sourceCoverageBatch20 = sourceCoverageTargetSlice20A ++
      sourceCoverageTargetSlice20B := by
  rfl

theorem sourceCoverageBatch20_targetConsistent :
    sourceCoverageBatch20.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch20_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice20A_targetConsistent,
    sourceCoverageTargetSlice20B_targetConsistent]
theorem sourceCoverageBatch20_length :
    sourceCoverageBatch20.length = 500 := by
  rw [sourceCoverageBatch20_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice20A_length,
    sourceCoverageTargetSlice20B_length]

end SmallCusp

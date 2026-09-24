import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch53_eq_targetSlices :
    sourceCoverageBatch53 = sourceCoverageTargetSlice53A ++
      sourceCoverageTargetSlice53B := by
  rfl

theorem sourceCoverageBatch53_targetConsistent :
    sourceCoverageBatch53.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch53_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice53A_targetConsistent,
    sourceCoverageTargetSlice53B_targetConsistent]
theorem sourceCoverageBatch53_length :
    sourceCoverageBatch53.length = 500 := by
  rw [sourceCoverageBatch53_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice53A_length,
    sourceCoverageTargetSlice53B_length]

end SmallCusp

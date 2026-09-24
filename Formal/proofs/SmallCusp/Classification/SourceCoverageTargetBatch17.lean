import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch17_eq_targetSlices :
    sourceCoverageBatch17 = sourceCoverageTargetSlice17A ++
      sourceCoverageTargetSlice17B := by
  rfl

theorem sourceCoverageBatch17_targetConsistent :
    sourceCoverageBatch17.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch17_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice17A_targetConsistent,
    sourceCoverageTargetSlice17B_targetConsistent]
theorem sourceCoverageBatch17_length :
    sourceCoverageBatch17.length = 500 := by
  rw [sourceCoverageBatch17_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice17A_length,
    sourceCoverageTargetSlice17B_length]

end SmallCusp

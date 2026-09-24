import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch18_eq_targetSlices :
    sourceCoverageBatch18 = sourceCoverageTargetSlice18A ++
      sourceCoverageTargetSlice18B := by
  rfl

theorem sourceCoverageBatch18_targetConsistent :
    sourceCoverageBatch18.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch18_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice18A_targetConsistent,
    sourceCoverageTargetSlice18B_targetConsistent]
theorem sourceCoverageBatch18_length :
    sourceCoverageBatch18.length = 500 := by
  rw [sourceCoverageBatch18_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice18A_length,
    sourceCoverageTargetSlice18B_length]

end SmallCusp

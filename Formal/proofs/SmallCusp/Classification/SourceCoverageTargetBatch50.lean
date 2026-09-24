import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace SmallCusp

theorem sourceCoverageBatch50_eq_targetSlices :
    sourceCoverageBatch50 = sourceCoverageTargetSlice50A ++
      sourceCoverageTargetSlice50B := by
  rfl

theorem sourceCoverageBatch50_targetConsistent :
    sourceCoverageBatch50.all
      (fun R => decide R.TargetConsistent) = true := by
  rw [sourceCoverageBatch50_eq_targetSlices]
  simp [
    sourceCoverageTargetSlice50A_targetConsistent,
    sourceCoverageTargetSlice50B_targetConsistent]
theorem sourceCoverageBatch50_length :
    sourceCoverageBatch50.length = 500 := by
  rw [sourceCoverageBatch50_eq_targetSlices, List.length_append,
    sourceCoverageTargetSlice50A_length,
    sourceCoverageTargetSlice50B_length]

end SmallCusp

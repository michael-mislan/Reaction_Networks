import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A1

namespace SmallCusp

def sourceCoverageTargetSlice29A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29A0 ++
  sourceCoverageTargetSlice29A1

theorem sourceCoverageTargetSlice29A_targetConsistent :
    sourceCoverageTargetSlice29A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29A,
    sourceCoverageTargetSlice29A0_targetConsistent,
    sourceCoverageTargetSlice29A1_targetConsistent]

theorem sourceCoverageTargetSlice29A_length : sourceCoverageTargetSlice29A.length = 250 := by
  simp [sourceCoverageTargetSlice29A,
    sourceCoverageTargetSlice29A0_length,
    sourceCoverageTargetSlice29A1_length]

end SmallCusp

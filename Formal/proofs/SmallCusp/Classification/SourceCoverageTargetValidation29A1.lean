import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A11

namespace SmallCusp

def sourceCoverageTargetSlice29A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29A10 ++
  sourceCoverageTargetSlice29A11

theorem sourceCoverageTargetSlice29A1_targetConsistent :
    sourceCoverageTargetSlice29A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29A1,
    sourceCoverageTargetSlice29A10_targetConsistent,
    sourceCoverageTargetSlice29A11_targetConsistent]

theorem sourceCoverageTargetSlice29A1_length : sourceCoverageTargetSlice29A1.length = 125 := by
  simp [sourceCoverageTargetSlice29A1,
    sourceCoverageTargetSlice29A10_length,
    sourceCoverageTargetSlice29A11_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29A01

namespace SmallCusp

def sourceCoverageTargetSlice29A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29A00 ++
  sourceCoverageTargetSlice29A01

theorem sourceCoverageTargetSlice29A0_targetConsistent :
    sourceCoverageTargetSlice29A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29A0,
    sourceCoverageTargetSlice29A00_targetConsistent,
    sourceCoverageTargetSlice29A01_targetConsistent]

theorem sourceCoverageTargetSlice29A0_length : sourceCoverageTargetSlice29A0.length = 125 := by
  simp [sourceCoverageTargetSlice29A0,
    sourceCoverageTargetSlice29A00_length,
    sourceCoverageTargetSlice29A01_length]

end SmallCusp

import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A11

namespace SmallCusp

def sourceCoverageTargetSlice35A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35A10 ++
  sourceCoverageTargetSlice35A11

theorem sourceCoverageTargetSlice35A1_targetConsistent :
    sourceCoverageTargetSlice35A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35A1,
    sourceCoverageTargetSlice35A10_targetConsistent,
    sourceCoverageTargetSlice35A11_targetConsistent]

theorem sourceCoverageTargetSlice35A1_length : sourceCoverageTargetSlice35A1.length = 125 := by
  simp [sourceCoverageTargetSlice35A1,
    sourceCoverageTargetSlice35A10_length,
    sourceCoverageTargetSlice35A11_length]

end SmallCusp

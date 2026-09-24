import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A1

namespace SmallCusp

def sourceCoverageTargetSlice35A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35A0 ++
  sourceCoverageTargetSlice35A1

theorem sourceCoverageTargetSlice35A_targetConsistent :
    sourceCoverageTargetSlice35A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35A,
    sourceCoverageTargetSlice35A0_targetConsistent,
    sourceCoverageTargetSlice35A1_targetConsistent]

theorem sourceCoverageTargetSlice35A_length : sourceCoverageTargetSlice35A.length = 250 := by
  simp [sourceCoverageTargetSlice35A,
    sourceCoverageTargetSlice35A0_length,
    sourceCoverageTargetSlice35A1_length]

end SmallCusp

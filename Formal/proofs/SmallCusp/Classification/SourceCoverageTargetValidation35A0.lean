import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35A01

namespace SmallCusp

def sourceCoverageTargetSlice35A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35A00 ++
  sourceCoverageTargetSlice35A01

theorem sourceCoverageTargetSlice35A0_targetConsistent :
    sourceCoverageTargetSlice35A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35A0,
    sourceCoverageTargetSlice35A00_targetConsistent,
    sourceCoverageTargetSlice35A01_targetConsistent]

theorem sourceCoverageTargetSlice35A0_length : sourceCoverageTargetSlice35A0.length = 125 := by
  simp [sourceCoverageTargetSlice35A0,
    sourceCoverageTargetSlice35A00_length,
    sourceCoverageTargetSlice35A01_length]

end SmallCusp

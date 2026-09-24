import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A01

namespace SmallCusp

def sourceCoverageTargetSlice53A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53A00 ++
  sourceCoverageTargetSlice53A01

theorem sourceCoverageTargetSlice53A0_targetConsistent :
    sourceCoverageTargetSlice53A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53A0,
    sourceCoverageTargetSlice53A00_targetConsistent,
    sourceCoverageTargetSlice53A01_targetConsistent]

theorem sourceCoverageTargetSlice53A0_length : sourceCoverageTargetSlice53A0.length = 125 := by
  simp [sourceCoverageTargetSlice53A0,
    sourceCoverageTargetSlice53A00_length,
    sourceCoverageTargetSlice53A01_length]

end SmallCusp

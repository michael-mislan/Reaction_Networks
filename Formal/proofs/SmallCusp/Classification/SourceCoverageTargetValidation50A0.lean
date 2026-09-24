import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A01

namespace SmallCusp

def sourceCoverageTargetSlice50A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50A00 ++
  sourceCoverageTargetSlice50A01

theorem sourceCoverageTargetSlice50A0_targetConsistent :
    sourceCoverageTargetSlice50A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50A0,
    sourceCoverageTargetSlice50A00_targetConsistent,
    sourceCoverageTargetSlice50A01_targetConsistent]

theorem sourceCoverageTargetSlice50A0_length : sourceCoverageTargetSlice50A0.length = 125 := by
  simp [sourceCoverageTargetSlice50A0,
    sourceCoverageTargetSlice50A00_length,
    sourceCoverageTargetSlice50A01_length]

end SmallCusp

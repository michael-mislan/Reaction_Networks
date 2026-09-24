import proofs.SmallCusp.Classification.CoverageTypes
import proofs.SmallCusp.Classification.SourceCoverageBatch50

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def sourceCoverageTargetSlice50B11PartA : List SourceCoverageRecord :=
  [
  { sourceIndices := ![6, 12, 19, 26, 28]
    targetIndices := ![6, 12, 18, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8232
    swapTarget := false },
  { sourceIndices := ![6, 12, 19, 26, 29]
    targetIndices := ![6, 12, 18, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8232
    swapTarget := false },
  { sourceIndices := ![6, 12, 19, 27, 28]
    targetIndices := ![6, 12, 18, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8234
    swapTarget := false },
  { sourceIndices := ![6, 12, 19, 27, 29]
    targetIndices := ![6, 12, 18, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8234
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 21, 25]
    targetIndices := ![6, 12, 20, 21, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8274
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 21, 26]
    targetIndices := ![6, 12, 20, 21, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8273
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 21, 27]
    targetIndices := ![6, 12, 20, 21, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8274
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 21, 28]
    targetIndices := ![6, 12, 20, 21, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8275
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 21, 29]
    targetIndices := ![6, 12, 20, 21, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8275
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 22, 25]
    targetIndices := ![6, 12, 20, 22, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8280
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 22, 26]
    targetIndices := ![6, 12, 20, 22, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8279
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 22, 27]
    targetIndices := ![6, 12, 20, 22, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8280
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 22, 28]
    targetIndices := ![6, 12, 20, 22, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8281
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 22, 29]
    targetIndices := ![6, 12, 20, 22, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8281
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 23, 25]
    targetIndices := ![6, 12, 20, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8277
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 23, 26]
    targetIndices := ![6, 12, 20, 23, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8276
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 23, 27]
    targetIndices := ![6, 12, 20, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8277
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 23, 28]
    targetIndices := ![6, 12, 20, 23, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8278
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 23, 29]
    targetIndices := ![6, 12, 20, 23, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8278
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 24, 25]
    targetIndices := ![6, 12, 20, 24, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8283
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 24, 26]
    targetIndices := ![6, 12, 20, 24, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8282
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 24, 27]
    targetIndices := ![6, 12, 20, 24, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8283
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 24, 28]
    targetIndices := ![6, 12, 20, 24, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8284
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 24, 29]
    targetIndices := ![6, 12, 20, 24, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8284
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 25, 26]
    targetIndices := ![6, 12, 20, 25, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8285
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 25, 27]
    targetIndices := ![6, 12, 20, 25, 27]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8287
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 25, 28]
    targetIndices := ![6, 12, 20, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8288
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 25, 29]
    targetIndices := ![6, 12, 20, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8288
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 26, 27]
    targetIndices := ![6, 12, 20, 25, 26]
    matching := ![0, 1, 2, 4, 3]
    outcome := .determinant
    targetIndex := 8285
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 26, 28]
    targetIndices := ![6, 12, 20, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8286
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 26, 29]
    targetIndices := ![6, 12, 20, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8286
    swapTarget := false },
]

def sourceCoverageTargetSlice50B11PartB : List SourceCoverageRecord :=
  [
  { sourceIndices := ![6, 12, 20, 27, 28]
    targetIndices := ![6, 12, 20, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8288
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 27, 29]
    targetIndices := ![6, 12, 20, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8288
    swapTarget := false },
  { sourceIndices := ![6, 12, 20, 28, 29]
    targetIndices := ![6, 12, 20, 28, 29]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8289
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 22, 25]
    targetIndices := ![6, 12, 21, 22, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8294
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 22, 26]
    targetIndices := ![6, 12, 21, 22, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8293
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 22, 27]
    targetIndices := ![6, 12, 21, 22, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8294
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 22, 28]
    targetIndices := ![6, 12, 21, 22, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8295
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 22, 29]
    targetIndices := ![6, 12, 21, 22, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8295
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 23, 25]
    targetIndices := ![6, 12, 21, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8291
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 23, 26]
    targetIndices := ![6, 12, 21, 23, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8290
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 23, 27]
    targetIndices := ![6, 12, 21, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8291
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 23, 28]
    targetIndices := ![6, 12, 21, 23, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8292
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 23, 29]
    targetIndices := ![6, 12, 21, 23, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8292
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 24, 25]
    targetIndices := ![6, 12, 21, 24, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8297
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 24, 26]
    targetIndices := ![6, 12, 21, 24, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8296
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 24, 27]
    targetIndices := ![6, 12, 21, 24, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8297
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 24, 28]
    targetIndices := ![6, 12, 21, 24, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8298
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 24, 29]
    targetIndices := ![6, 12, 21, 24, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8298
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 25, 26]
    targetIndices := ![6, 12, 21, 25, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8299
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 25, 27]
    targetIndices := ![6, 12, 21, 25, 27]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8301
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 25, 28]
    targetIndices := ![6, 12, 21, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8302
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 25, 29]
    targetIndices := ![6, 12, 21, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8302
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 26, 27]
    targetIndices := ![6, 12, 21, 25, 26]
    matching := ![0, 1, 2, 4, 3]
    outcome := .determinant
    targetIndex := 8299
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 26, 28]
    targetIndices := ![6, 12, 21, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8300
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 26, 29]
    targetIndices := ![6, 12, 21, 26, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8300
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 27, 28]
    targetIndices := ![6, 12, 21, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8302
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 27, 29]
    targetIndices := ![6, 12, 21, 25, 28]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8302
    swapTarget := false },
  { sourceIndices := ![6, 12, 21, 28, 29]
    targetIndices := ![6, 12, 21, 28, 29]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8303
    swapTarget := false },
  { sourceIndices := ![6, 12, 22, 23, 25]
    targetIndices := ![6, 12, 22, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8305
    swapTarget := false },
  { sourceIndices := ![6, 12, 22, 23, 26]
    targetIndices := ![6, 12, 22, 23, 26]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8304
    swapTarget := false },
  { sourceIndices := ![6, 12, 22, 23, 27]
    targetIndices := ![6, 12, 22, 23, 25]
    matching := ![0, 1, 2, 3, 4]
    outcome := .determinant
    targetIndex := 8305
    swapTarget := false }]

def sourceCoverageTargetSlice50B11 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50B11PartA ++ sourceCoverageTargetSlice50B11PartB

theorem sourceCoverageTargetSlice50B11PartA_targetConsistent :
    sourceCoverageTargetSlice50B11PartA.all (fun R => decide R.TargetConsistent) = true := by
  decide

theorem sourceCoverageTargetSlice50B11PartB_targetConsistent :
    sourceCoverageTargetSlice50B11PartB.all (fun R => decide R.TargetConsistent) = true := by
  decide

theorem sourceCoverageTargetSlice50B11PartA_length : sourceCoverageTargetSlice50B11PartA.length = 31 := by
  decide

theorem sourceCoverageTargetSlice50B11PartB_length : sourceCoverageTargetSlice50B11PartB.length = 31 := by
  decide

theorem sourceCoverageTargetSlice50B11_targetConsistent :
    sourceCoverageTargetSlice50B11.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50B11,
    sourceCoverageTargetSlice50B11PartA_targetConsistent,
    sourceCoverageTargetSlice50B11PartB_targetConsistent]

theorem sourceCoverageTargetSlice50B11_length : sourceCoverageTargetSlice50B11.length = 62 := by
  simp [sourceCoverageTargetSlice50B11,
    sourceCoverageTargetSlice50B11PartA_length,
    sourceCoverageTargetSlice50B11PartB_length]

end SmallCusp

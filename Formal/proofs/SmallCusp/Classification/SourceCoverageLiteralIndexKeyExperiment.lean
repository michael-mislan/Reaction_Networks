import proofs.SmallCusp.Classification.SourceCoverageSourceIndices00
import proofs.SmallCusp.Classification.SourceCoverageSourceKeys00
import proofs.SmallCusp.Classification.SourceCoverageSourceKeysSwapped00
import proofs.SmallCusp.Classification.SourceKeyWeights

namespace SmallCusp

def sourceKeyFromIndexRow (row : Array Nat) : Nat :=
  (row.toList.map (fun i => sourceBitWeights[i]!)).sum

def sourceSwappedKeyFromIndexRow (row : Array Nat) : Nat :=
  (row.toList.map (fun i => sourceSwappedBitWeights[i]!)).sum

def sourceCoverageSourceIndices00KeysValid : Bool :=
  sourceCoverageSourceIndices00.map sourceKeyFromIndexRow == sourceCoverageSourceKeys00 &&
    sourceCoverageSourceIndices00.map sourceSwappedKeyFromIndexRow ==
      sourceCoverageSourceKeysSwapped00

theorem source_coverage_literal_index_keys_match :
    sourceCoverageSourceIndices00KeysValid = true := by
  native_decide

end SmallCusp

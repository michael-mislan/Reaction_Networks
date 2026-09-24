import proofs.SmallCusp.Classification.LightCoverageTypes

namespace SmallCusp

def sourceBitWeights : Array Nat :=
  #[2, 4, 8, 16, 32, 64, 256, 512, 1024, 2048, 4096, 8192,
    32768, 65536, 131072, 262144, 524288, 1048576, 4194304, 8388608,
    16777216, 33554432, 67108864, 134217728, 536870912, 1073741824,
    2147483648, 4294967296, 8589934592, 17179869184]

def sourceSwappedBitWeights : Array Nat :=
  #[4, 2, 32, 16, 8, 4096, 8192, 131072, 65536, 32768, 64, 256,
    2048, 1024, 512, 1073741824, 4294967296, 2147483648, 17179869184,
    8589934592, 16777216, 67108864, 33554432, 536870912, 134217728,
    262144, 1048576, 524288, 8388608, 4194304]

def sourceBitWeight (i : Fin 30) : Nat := sourceBitWeights[i.val]!

def sourceSwappedBitWeight (i : Fin 30) : Nat :=
  sourceSwappedBitWeights[i.val]!

theorem source_bit_weight_eq (i : Fin 30) :
    sourceBitWeight i = 2 ^ bimolReactionIndex (bimolReactionCatalogue i) := by
  fin_cases i <;> decide

theorem source_swapped_bit_weight_eq (i : Fin 30) :
    sourceSwappedBitWeight i =
      2 ^ bimolReactionIndex (swapBimolReaction (bimolReactionCatalogue i)) := by
  fin_cases i <;> decide

end SmallCusp

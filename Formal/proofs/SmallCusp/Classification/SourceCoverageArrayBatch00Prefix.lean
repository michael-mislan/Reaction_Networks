import Mathlib.Data.List.PeriodicityLemma
import proofs.SmallCusp.Classification.SourceCoverageSources
import proofs.SmallCusp.Classification.SourceCoverageTargetBatch00

namespace SmallCusp

theorem source_coverage_array_batch00_prefix
    (i : Fin 500) :
    sourceCoverageArray[i.val]? = sourceCoverageBatch00.toArray[i.val]? := by
  simp [sourceCoverageArray, sourceCoverageRecords,
    sourceCoverageValidation00Records, sourceCoverageBatch00_length,
    List.getElem?_append_left]

end SmallCusp

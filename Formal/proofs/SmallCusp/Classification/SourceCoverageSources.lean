import proofs.SmallCusp.Classification.SourceCoverageValidation00

namespace SmallCusp

def sourceCoverageRecords : List SourceCoverageRecord :=
  sourceCoverageValidation00Records

@[irreducible] def sourceCoverageArray : Array SourceCoverageRecord := sourceCoverageRecords.toArray

end SmallCusp

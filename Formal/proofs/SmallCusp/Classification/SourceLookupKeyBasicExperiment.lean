import proofs.SmallCusp.Classification.SourceLookupCore

namespace SmallCusp

def sourceLookupKeyListBasic : List Nat :=
  sourceLookupEntries.toList.map Prod.fst

theorem sourceLookupEntries_size_basic : sourceLookupEntries.size = 60036 := by
  native_decide

theorem sourceLookupKeyList_nodup_basic : sourceLookupKeyListBasic.Nodup := by
  native_decide

end SmallCusp

import proofs.SmallCusp.Classification.SourceLookupCore

namespace SmallCusp

theorem all_source_lookup_searches_self :
    ∀ i : Fin sourceLookupEntries.size,
      sourceLookupSearch sourceLookupEntries 20
          (sourceLookupEntries[i.val]!).1 0 sourceLookupEntries.size =
        some (sourceLookupEntries[i.val]!).2 := by
  native_decide

end SmallCusp

import proofs.SmallCusp.Classification.SourceLookupCore

namespace SmallCusp

theorem source_lookup_search_key_mem
    (entries : Array (Nat × Nat × Bool)) (fuel key lo hi : Nat)
    (payload : Nat × Bool)
    (h : sourceLookupSearch entries fuel key lo hi = some payload) :
    ∃ entry ∈ entries, entry.1 = key := by
  induction fuel generalizing lo hi with
  | zero => simp [sourceLookupSearch] at h
  | succ fuel ih =>
      simp only [sourceLookupSearch] at h
      by_cases hlt : lo < hi
      · simp only [hlt, if_true] at h
        cases hget : entries[(lo + hi) / 2]? with
        | none => simp [hget] at h
        | some entry =>
            simp only [hget] at h
            by_cases hk : key = entry.1
            · exact ⟨entry, Array.mem_of_getElem? hget, hk.symm⟩
            · simp only [hk, if_false] at h
              split at h <;> exact ih _ _ h
      · simp [hlt] at h

end SmallCusp

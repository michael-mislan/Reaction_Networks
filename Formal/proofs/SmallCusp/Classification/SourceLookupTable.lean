import Mathlib
import proofs.SmallCusp.Classification.SourceLookupEncoded

namespace SmallCusp

def parseSourceLookupRow (s : String) : Option (Nat × Nat × Bool) := do
  match s.splitOn "," with
  | [key, index, flag] =>
      let k ← key.toNat?
      let i ← index.toNat?
      if flag = "0" then return (k, i, false)
      else if flag = "1" then return (k, i, true)
      else none
  | _ => none

@[irreducible] def sourceLookupEntries : Array (Nat × Nat × Bool) :=
  (sourceLookupEncoded.flatMap (fun s =>
    (s.splitOn ";").filterMap parseSourceLookupRow)).toArray

end SmallCusp

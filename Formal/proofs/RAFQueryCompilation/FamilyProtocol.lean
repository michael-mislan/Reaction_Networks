import proofs.RAFQueryCompilation.FamilyPointReuse

namespace RAFQueryCompilation.ModuleFamily
open RAF

def pairMask {n : ℕ} (i : Fin n) (left right : Bool) : Finset (Fin (n*2+1)) :=
  (if left then {reactionCode n (some (i,false))} else ∅) ∪
  (if right then {reactionCode n (some (i,true))} else ∅)

theorem pairMask_subset {n : ℕ} (i : Fin n) (a b : Bool) :
    pairMask i a b ⊆ indexedRegion i := by
  cases a <;> cases b <;> simp [pairMask,indexedRegion,region]

def packetEdit {n : ℕ} (i : Fin n) (a b c d : Bool) : PairEdit n where
  pair := i
  removed := pairMask i a b
  added := pairMask i c d
  localEdits := Finset.union_subset (pairMask_subset i a b) (pairMask_subset i c d)

/-- Five natural-number words: pair index, two removal bits, two addition bits.
This is a word-level decoder, not an unpriced JSON parser. -/
def decodePairEdit (n : ℕ) : List ℕ → Option (PairEdit n)
  | [i,a,b,c,d] =>
    if hi : i < n then
      if a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 then
        some (packetEdit ⟨i,hi⟩ (decide (a=1)) (decide (b=1)) (decide (c=1)) (decide (d=1)))
      else none
    else none
  | _ => none

def encodePairEdit {n : ℕ} (e : PairEdit n) : List ℕ :=
  [e.pair.val,
   if reactionCode n (some (e.pair,false)) ∈ e.removed then 1 else 0,
   if reactionCode n (some (e.pair,true)) ∈ e.removed then 1 else 0,
   if reactionCode n (some (e.pair,false)) ∈ e.added then 1 else 0,
   if reactionCode n (some (e.pair,true)) ∈ e.added then 1 else 0]

theorem pairMask_reconstruct {n : ℕ} (i : Fin n) (S : Finset (Fin (n*2+1)))
    (h : S ⊆ indexedRegion i) :
    pairMask i (decide (reactionCode n (some (i,false)) ∈ S))
      (decide (reactionCode n (some (i,true)) ∈ S)) = S := by
  ext r
  have hr : r ∈ S → r = reactionCode n (some (i,false)) ∨
      r = reactionCode n (some (i,true)) := by
    intro hs
    have := h hs
    simpa [indexedRegion,region] using this
  simp only [pairMask,Finset.mem_union]
  by_cases hl : reactionCode n (some (i,false)) ∈ S <;>
    by_cases hh : reactionCode n (some (i,true)) ∈ S <;>
      simp [hl,hh] <;> aesop

theorem decode_encode_pairEdit {n : ℕ} (e : PairEdit n) :
    decodePairEdit n (encodePairEdit e) = some e := by
  have hd : e.removed ⊆ indexedRegion e.pair :=
    Finset.Subset.trans Finset.subset_union_left e.localEdits
  have ha : e.added ⊆ indexedRegion e.pair :=
    Finset.Subset.trans Finset.subset_union_right e.localEdits
  have hm := pairMask_reconstruct e.pair e.removed hd
  have hp := pairMask_reconstruct e.pair e.added ha
  simp only [encodePairEdit,decodePairEdit,dif_pos e.pair.isLt]
  split_ifs <;> simp_all [packetEdit] <;> cases e <;> simp_all

theorem encoded_pair_words {n : ℕ} (e : PairEdit n) : (encodePairEdit e).length = 5 := rfl

theorem generated_certificate_size {n : ℕ} (e : PairEdit n) :
    (indexedCertificate e.pair).length = 2 ∧
    (indexedCertificate e.pair).flatten.length = 2 := by
  simp [indexedCertificate,pairCertificate]

end RAFQueryCompilation.ModuleFamily

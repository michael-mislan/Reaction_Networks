import proofs.RAFQueryCompilation.FamilyWordBatch
import proofs.RAFQueryCompilation.FamilyCode

namespace RAFQueryCompilation.ModuleFamily
open RAF

def directPairMask {n : ℕ} (i : Fin n) (left right : Bool) : Finset (Fin (n*2+1)) :=
  (if left then {arithmeticReactionCode (some (i,false))} else ∅) ∪
  (if right then {arithmeticReactionCode (some (i,true))} else ∅)

theorem directPairMask_subset {n : ℕ} (i : Fin n) (a b : Bool) :
    directPairMask i a b ⊆ indexedRegion i := by
  cases a <;> cases b <;> simp [directPairMask,arithmeticReactionCode_eq,indexedRegion,region]

def directPacketEdit {n : ℕ} (i : Fin n) (a b c d : Bool) : PairEdit n where
  pair := i
  removed := directPairMask i a b
  added := directPairMask i c d
  localEdits := Finset.union_subset (directPairMask_subset i a b) (directPairMask_subset i c d)

/-- Five natural-number words: pair index, two removal bits, two addition bits.
This is a word-level decoder, not an unpriced JSON parser. -/
def directDecodePairEdit (n : ℕ) : List ℕ → Option (PairEdit n)
  | [i,a,b,c,d] =>
    if hi : i < n then
      if a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1 then
        some (directPacketEdit ⟨i,hi⟩ (decide (a=1)) (decide (b=1)) (decide (c=1)) (decide (d=1)))
      else none
    else none
  | _ => none

def familyArithmeticBatch {n : ℕ} (codeFee : ℕ)
    (cache : CompiledSource (n*2+1+1) (n*2+1)) :
    List (List ℕ) → QueryState (n*2+1+1) (n*2+1) → Option (FamilyPointResult n)
  | [], state => some ⟨[],state,0⟩
  | words::rest, state =>
    match directDecodePairEdit n words with
    | none => none
    | some e =>
      let step := hybridQuery (indexedSource n) (indexedCats n)
        (fun r => cache.successors[r.val]) (fun r => cache.needs[r.val]) state
        e.removed e.added (directPairMask e.pair true true) [[arithmeticReactionCode (some (e.pair,false)), arithmeticReactionCode (some (e.pair,true))], []] 1011
      let answer := step.1.answer[(arithmeticReactionCode (some (e.pair,true))).val]
      (familyArithmeticBatch codeFee cache rest step.1).map fun tail =>
        ⟨answer::tail.members,tail.state,
          step.2+2+familyProtocolCharge codeFee e+tail.charge⟩


theorem directDecodePairEdit_eq (n : ℕ) (words : List ℕ) :
    directDecodePairEdit n words = decodePairEdit n words := by
  have hp : directPacketEdit (n := n) = packetEdit := by
    funext i a b c d
    simp only [directPacketEdit,packetEdit,directPairMask,pairMask,arithmeticReactionCode_eq]
  simp only [directDecodePairEdit,decodePairEdit,hp]
  rfl

theorem familyArithmeticBatch_eq {n : ℕ} (codeFee : ℕ)
    (cache : CompiledSource (n*2+1+1) (n*2+1)) (packets : List (List ℕ))
    (state : QueryState (n*2+1+1) (n*2+1)) :
    familyArithmeticBatch codeFee cache packets state = familyWordBatch codeFee cache packets state := by
  have hr (i : Fin n) : directPairMask i true true = indexedRegion i := by
    simp [directPairMask,arithmeticReactionCode_eq,indexedRegion,region]
  induction packets generalizing state with
  | nil => rfl
  | cons words rest ih =>
    simp only [familyArithmeticBatch,familyWordBatch,directDecodePairEdit_eq,hr,
      arithmeticReactionCode_eq,indexedCertificate,pairCertificate,List.map_cons,List.map_nil,ih]
    rfl

/-- Eight abstract units per forward code call: option dispatch, pair access,
bit choice, multiplication, two additions, value extraction and result return.
This is a word-operation tariff; it does not count native instructions. -/
def familyArithmeticRun {n : ℕ} (A : Finset (Fin (n*2+1)))
    (packets : List (List ℕ)) : Option (FamilyPointResult n) :=
  let cache := compileSource (indexedSource n) (indexedCats n) A
  (familyArithmeticBatch 8 cache packets cache.state).map fun result =>
    { result with charge := cache.charge+result.charge }

theorem familyArithmeticRun_eq {n : ℕ} (A : Finset (Fin (n*2+1)))
    (packets : List (List ℕ)) : familyArithmeticRun A packets = familyWordRun 8 A packets := by
  simp only [familyArithmeticRun,familyWordRun,familyArithmeticBatch_eq]

theorem familyArithmeticRun_saves {n : ℕ} (A : Finset (Fin (n*2+1)))
    (edits : List (PairEdit n))
    (h : familySetupCap n+1149*edits.length < (n*2+1)*edits.length) :
    ∃ result, familyArithmeticRun A (edits.map encodePairEdit) = some result ∧
      result.members = familyPointTrace edits A ∧
      result.charge < (familyPointBaseline edits
        (compileSource (indexedSource n) (indexedCats n) A).state.available).charge := by
  obtain ⟨result,hr,hm,hc⟩ := familyWordRun_correct_bound 8 A edits
  refine ⟨result, ?_,hm, ?_⟩
  · simpa only [familyArithmeticRun_eq] using hr
  · have hb := familyPointBaseline_reads edits
      (compileSource (indexedSource n) (indexedCats n) A).state.available
    norm_num at hc
    omega

end RAFQueryCompilation.ModuleFamily

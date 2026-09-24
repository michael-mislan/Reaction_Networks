import proofs.RAFQueryCompilation.FamilyCachedBatch

namespace RAFQueryCompilation.ModuleFamily
open RAF

/-- Explicit extension of the existing abstract charge, not native time.
The fixed terms count six packet spine inspections, five validity comparisons,
four bit conversions, four selection branches, one edit record, two dispatches,
eight certificate list cells and six empty-list constructions. `codeFee` prices
one reactionCode invocation. The three squares budget the two edit-set builders
and the two-element region builder. Five code calls generate region, certificate
and queried reaction; selected edit entries account for the others. -/
def familyProtocolCharge {n : ℕ} (codeFee : ℕ) (e : PairEdit n) : ℕ :=
  (6+5+4+4+1+2+8+6) +
  codeFee*(e.removed.card+e.added.card+5) +
  (e.removed.card+1)^2+(e.added.card+1)^2+9

theorem familyProtocolCharge_bound {n : ℕ} (codeFee : ℕ) (e : PairEdit n) :
    familyProtocolCharge codeFee e ≤ 63+9*codeFee := by
  have hr := Finset.card_le_card
    (Finset.Subset.trans Finset.subset_union_left e.localEdits)
  have ha := Finset.card_le_card
    (Finset.Subset.trans Finset.subset_union_right e.localEdits)
  simp only [indexed_region_card] at hr ha
  have hcode : codeFee*(e.removed.card+e.added.card+5) ≤ codeFee*9 :=
    Nat.mul_le_mul_left _ (by omega)
  have hrr : (e.removed.card+1)^2 ≤ 9 := by nlinarith
  have haa : (e.added.card+1)^2 ≤ 9 := by nlinarith
  unfold familyProtocolCharge
  nlinarith

/-- One decoded record is consumed immediately. A malformed word packet rejects
the batch. The theorem below covers every encoded valid edit sequence. Byte
parsing, arbitrary-precision arithmetic and native ownership are separate. -/
def familyWordBatch {n : ℕ} (codeFee : ℕ)
    (cache : CompiledSource (n*2+1+1) (n*2+1)) :
    List (List ℕ) → QueryState (n*2+1+1) (n*2+1) → Option (FamilyPointResult n)
  | [], state => some ⟨[],state,0⟩
  | words::rest, state =>
    match decodePairEdit n words with
    | none => none
    | some e =>
      let step := hybridQuery (indexedSource n) (indexedCats n)
        (fun r => cache.successors[r.val]) (fun r => cache.needs[r.val]) state
        e.removed e.added (indexedRegion e.pair) (indexedCertificate e.pair) 1011
      let answer := step.1.answer[(reactionCode n (some (e.pair,true))).val]
      (familyWordBatch codeFee cache rest step.1).map fun tail =>
        ⟨answer::tail.members,tail.state,
          step.2+2+familyProtocolCharge codeFee e+tail.charge⟩

def familyProtocolTotal {n : ℕ} (codeFee : ℕ) (edits : List (PairEdit n)) : ℕ :=
  (edits.map (familyProtocolCharge codeFee)).sum

theorem familyWordBatch_refines {n : ℕ} (codeFee : ℕ)
    (cache : CompiledSource (n*2+1+1) (n*2+1)) (edits : List (PairEdit n))
    (state : QueryState (n*2+1+1) (n*2+1)) :
    familyWordBatch codeFee cache (edits.map encodePairEdit) state =
      some { familyCachedPointReuse cache edits state with charge :=
        (familyCachedPointReuse cache edits state).charge+familyProtocolTotal codeFee edits } := by
  induction edits generalizing state with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons,familyWordBatch,decode_encode_pairEdit,ih,
      Option.map_some,familyCachedPointReuse,familyProtocolTotal,List.map_cons,List.sum_cons]
    congr 2; omega

theorem familyProtocolTotal_bound {n : ℕ} (codeFee : ℕ) (edits : List (PairEdit n)) :
    familyProtocolTotal codeFee edits ≤ (63+9*codeFee)*edits.length := by
  induction edits with
  | nil => simp [familyProtocolTotal]
  | cons e rest ih =>
    have h := familyProtocolCharge_bound codeFee e
    simp only [familyProtocolTotal,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def familyWordRun {n : ℕ} (codeFee : ℕ) (A : Finset (Fin (n*2+1)))
    (packets : List (List ℕ)) : Option (FamilyPointResult n) :=
  let cache := compileSource (indexedSource n) (indexedCats n) A
  (familyWordBatch codeFee cache packets cache.state).map fun result =>
    { result with charge := cache.charge+result.charge }

theorem familyWordRun_correct_bound {n : ℕ} (codeFee : ℕ)
    (A : Finset (Fin (n*2+1))) (edits : List (PairEdit n)) :
    ∃ result, familyWordRun codeFee A (edits.map encodePairEdit) = some result ∧
      result.members = familyPointTrace edits A ∧
      result.charge ≤ familySetupCap n+(1077+9*codeFee)*edits.length := by
  let result := { familyCachedRun A edits with charge :=
    (familyCachedRun A edits).charge+familyProtocolTotal codeFee edits }
  refine ⟨result, ?_, ?_, ?_⟩
  · simp only [familyWordRun,familyWordBatch_refines,Option.map_some,result,familyCachedRun]
    congr 2; omega
  · exact familyCachedRun_members A edits
  · have hc := familyCachedRun_bound A edits
    have hp := familyProtocolTotal_bound codeFee edits
    change (familyCachedRun A edits).charge+familyProtocolTotal codeFee edits ≤ _
    nlinarith

end RAFQueryCompilation.ModuleFamily

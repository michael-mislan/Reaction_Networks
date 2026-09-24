import proofs.RAFQueryCompilation.MeteredLocal
import proofs.RAFQueryCompilation.HybridQuery
import proofs.RAFQueryCompilation.PointQuery
import proofs.RAFQueryCompilation.CompiledSource
import proofs.RAFQueryCompilation.SupportPruning
import proofs.RAFQueryCompilation.SupportHybrid
import proofs.RAFQueryCompilation.IncidenceCompilation
import proofs.RAFQueryCompilation.RankedQuery
import proofs.RAFQueryCompilation.RankedLoss
import proofs.RAFQueryCompilation.SupportLoss
import proofs.RAFQueryCompilation.MaskedRankedWitness
import proofs.RAFQueryCompilation.MaskedPruning
import proofs.RAFQueryCompilation.RankedStartup
import proofs.RAFQueryCompilation.DirectLocalLoss
import Lean.Data.Json

namespace RAFQueryCompilation.Runtime
open RAF Lean

def readOrder (n : ℕ) (j : Json) : Except String (List (Fin n)) := do
  let xs ← j.getArr?
  xs.toList.mapM fun v => do
    let x ← v.getNat?
    if h : x < n then pure ⟨x, h⟩ else throw "index out of bounds"

def readSet (n : ℕ) (j : Json) : Except String (Finset (Fin n)) := do
  return (← readOrder n j).toFinset

def readRows (n : ℕ) (j : Json) : Except String (Array (Finset (Fin n))) := do
  (← j.getArr?).mapM (readSet n)

def readCertificate (m : ℕ) (j : Json) : Except String (List (List (Fin m))) := do
  (← j.getArr?).toList.mapM (readOrder m)

def field (j : Json) (name : String) : Except String Json := j.getObjVal? name

def readSupportCertificate (m : ℕ) (j : Json) : Except String (List (SupportRound m)) := do
  (← j.getArr?).toList.mapM fun row => do
    return { removals := ← readOrder m (← field row "removals")
             closureOrder := ← readOrder m (← field row "closure_order") }

/-- Batches may retain a reference or adopt each accepted query as the next state. -/
def runPacket (j : Json) : Except String Json := do
  let n ← (← field j "molecules").getNat?
  let inputs ← readRows n (← field j "inputs")
  let outputs ← readRows n (← field j "outputs")
  let cats ← readRows n (← field j "catalysts")
  let m := inputs.size
  if outputs.size != m || cats.size != m then throw "reaction row count mismatch"
  let food ← readSet n (← field j "food")
  let Q : CRS (Fin n) (Fin m) := {
    inputs := fun r => inputs[r.val]?.getD ∅
    outputs := fun r => outputs[r.val]?.getD ∅
    food := food }
  let C : Catalysis (Fin n) (Fin m) := fun x r => x ∈ cats[r.val]?.getD ∅
  let initial ← readSet m (← field j "initial_available")
  if (j.getObjValAs? Bool "witness_deletions").toOption.getD false then
    if (j.getObjValAs? Bool "sequential").toOption.getD false then
      throw "witness deletions use independent baseline queries"
    let parentRows ← readRows m (← field j "parents")
    let ranks ← (← (← field j "ranks").getArr?).mapM Json.getNat?
    if parentRows.size != m || ranks.size != m then throw "witness row count mismatch"
    let parents := fun r : Fin m => parentRows[r.val]?.getD ∅
    let rank := fun r : Fin m => ranks[r.val]?.getD 0
    let startup := if (j.getObjValAs? Bool "ranked_startup").toOption.getD true then
        rankedStartup Q (fun r => cats[r.val]?.getD ∅) initial parents rank
      else (if (j.getObjValAs? Bool "masked_pruning_startup").toOption.getD true then
        maskedFreshEvaluate Q (fun r => cats[r.val]?.getD ∅) initial
      else (freshEvaluate Q (fun r => cats[r.val]?.getD ∅) initial).1, false)
    let oldAnswer := startup.1
    let state := fastRebuildState Q initial oldAnswer
    if !startup.2 && !checkMaskedRankedSupport Q (fun r => cats[r.val]?.getD ∅)
        (fun r => state.answer[r.val]) parents rank then
      throw "ranked source witness rejected"
    let table := sourceConsumers parents
    let needs := Vector.ofFn (incidenceNeeds Q (fun r => cats[r.val]?.getD ∅))
    let mut answers : Array Json := #[]
    for query in (← (← field j "queries").getArr?) do
      let D ← readSet m (← field query "remove")
      let added ← readSet m ((query.getObjVal? "add").toOption.getD (Json.arr #[]))
      if added ≠ ∅ then throw "witness mode requires deletions only"
      if (j.getObjValAs? Bool "loss_profile").toOption.getD false then
        if let .ok supportJson := query.getObjVal? "support_certificate" then
          let supportCert ← readSupportCertificate m supportJson
          let result := supportLossTotal Q (fun r => cats[r.val]?.getD ∅) state D supportCert
          answers := answers.push (Json.mkObj [("lost", toJson ((result.1.sort (· ≤ ·)).map Fin.val)),
            ("used_witness", toJson false), ("used_support", toJson result.2)])
          continue
      let E ← readSet m (← field query "region")
      let cert ← readCertificate m (← field query "certificate")
      if (j.getObjValAs? Bool "loss_profile").toOption.getD false then
        let lossEvaluator := if (j.getObjValAs? Bool "direct_local_closure").toOption.getD true
          then directLocalLoss else rankedLossTotal
        let result := lossEvaluator Q (fun r => cats[r.val]?.getD ∅) table
          (fun r => needs[r.val]) state D E cert
        answers := answers.push (Json.mkObj [("lost", toJson ((result.1.sort (· ≤ ·)).map Fin.val)),
          ("used_witness", toJson result.2)])
        continue
      let probes ← readOrder m (← field query "probes")
      let result := rankedPointTotal Q (fun r => cats[r.val]?.getD ∅) table
        (fun r => needs[r.val]) state D E cert probes
      answers := answers.push (Json.mkObj [("members", toJson result.1),
        ("used_witness", toJson result.2)])
    return Json.mkObj [("queries", Json.arr answers), ("ranked_startup_accepted",toJson startup.2)]
  if (j.getObjValAs? Bool "support_pruning").toOption.getD false then
    let sequential := (j.getObjValAs? Bool "sequential").toOption.getD false
    let mut available := initial
    let mut answers : Array Json := #[]
    for query in (← (← field j "queries").getArr?) do
      let removed ← readSet m (← field query "remove")
      let added ← readSet m (← field query "add")
      let probes ← readOrder m (← field query "probes")
      let cert ← readSupportCertificate m (← field query "support_certificate")
      let nextAvailable := (available \ removed) ∪ added
      let some answer := checkSupportPruning Q (fun r => cats[r.val]?.getD ∅) nextAvailable cert
        | throw "support certificate rejected"
      answers := answers.push (Json.mkObj [
        ("accepted", toJson true),
        ("members", toJson (probes.map (fun r => decide (r ∈ answer))))])
      if sequential then available := nextAvailable
    return Json.mkObj [("queries", Json.arr answers)]
  if (j.getObjValAs? Bool "fresh_points").toOption.getD false then
    let sequential := (j.getObjValAs? Bool "sequential").toOption.getD false
    let mut available : Vector Bool m := Vector.ofFn (fun r => decide (r ∈ initial))
    let mut answers : Array Json := #[]
    for query in (← (← field j "queries").getArr?) do
      let removed ← readSet m (← field query "remove")
      let added ← readSet m (← field query "add")
      let probes ← readOrder m (← field query "probes")
      let result := freshPointQuery Q (fun r => cats[r.val]?.getD ∅) available removed added probes
      answers := answers.push (Json.mkObj [
        ("accepted", toJson true), ("members", toJson result.members),
        ("query_charge", toJson result.charge), ("probe_count", toJson probes.length)])
      if sequential then available := result.available
    return Json.mkObj [("queries", Json.arr answers)]
  let certifiedHybrid := (j.getObjValAs? Bool "support_hybrid").toOption.getD false
  let hybrid := (j.getObjValAs? Bool "hybrid").toOption.getD false || certifiedHybrid
  let startup ← if certifiedHybrid && (j.getObjValAs? Bool "incidence_startup").toOption.getD true then do
      let compiled := compileIncidenceSource Q (fun r => cats[r.val]?.getD ∅) initial
      pure (compiled.state, compiled.successors, compiled.needs, compiled.initialAnswer, (none : Option Nat))
    else do
      let compiled ← if hybrid then
          pure (compileSource Q (fun r => cats[r.val]?.getD ∅) initial)
        else do
          let initialCert ← readCertificate m (← field j "initial_certificate")
          let some oldAnswer := checkPruning Q C initial initialCert
            | throw "initial certificate rejected"
          pure ({ state := rebuildState Q initial oldAnswer
                  successors := Vector.ofFn (sourceSuccessors Q C)
                  needs := Vector.ofFn (sourceNeeds Q C)
                  initialAnswer := oldAnswer
                  charge := 0 } : CompiledSource n m)
      pure (compiled.state, compiled.successors, compiled.needs, compiled.initialAnswer,
        if hybrid then some compiled.charge else none)
  let (initialState, successorRows, needsRows, oldAnswer, setupCharge) := startup
  let sequential := (j.getObjValAs? Bool "sequential").toOption.getD false
  let mut currentOld := initialState.answer
  let mut currentAvailable := initialState.available
  let mut currentCounts := initialState.counts
  let queries ← (← field j "queries").getArr?
  let mut answers : Array Json := #[]
  for query in queries do
    let removed ← readSet m (← field query "remove")
    let added ← readSet m (← field query "add")
    let region ← readSet m (← field query "region")
    let cert ← readCertificate m (← field query "certificate")
    if hybrid then
      let probes ← readOrder m (← field query "probes")
      let budget := (query.getObjValAs? Nat "budget").toOption.getD m
      let state : QueryState n m := ⟨currentOld,currentAvailable,currentCounts⟩
      if certifiedHybrid then
        let fallbackCert ← readSupportCertificate m
          ((query.getObjVal? "support_certificate").toOption.getD (Json.arr #[]))
        let result := supportHybridQuery Q (fun r => cats[r.val]?.getD ∅)
          (fun r => successorRows[r.val]) (fun r => needsRows[r.val])
          state removed added region cert fallbackCert budget
        answers := answers.push (Json.mkObj [
          ("accepted", toJson true),
          ("members", toJson (probes.map (fun r => result.answer[r.val])))])
        if sequential then
          currentOld := result.answer
          currentAvailable := result.available
          currentCounts := result.counts
        continue
      let result := hybridQuery Q (fun r => cats[r.val]?.getD ∅)
        (fun r => successorRows[r.val]) (fun r => needsRows[r.val])
        state removed added region cert budget
      answers := answers.push (Json.mkObj [
        ("accepted", toJson true),
        ("members", toJson (probes.map (fun r => result.1.answer[r.val]))),
        ("consumer_charge", toJson result.2),
        ("query_charge", toJson (result.2+probes.length)),
        ("probe_count", toJson probes.length)])
      if sequential then
        currentOld := result.1.answer
        currentAvailable := result.1.available
        currentCounts := result.1.counts
      continue
    let availableMask := editedMask (fun r : Fin m => currentAvailable[r.val]) removed added
    let measured := meterLocal Q C (fun r => successorRows[r.val])
      (fun r => needsRows[r.val]) (fun r => currentOld[r.val]) availableMask
      (removed ∪ added) region (fun x => currentCounts[x.val]) cert
    let work := Json.mkObj [("rounds", toJson measured.rounds),
      ("row_budget", toJson measured.rowBudget),
      ("replay_entries", toJson measured.replayEntries)]
    match measured.answer with
    | none => answers := answers.push (Json.mkObj [("accepted", toJson false), ("work", work)])
    | some localAnswer =>
      answers := answers.push (Json.mkObj [
        ("accepted", toJson true),
        ("work", work),
        ("local_answer", toJson ((localAnswer.sort (· ≤ ·)).map Fin.val))])
      if sequential then
        let oldInside := maskRegion region (fun r => currentOld[r.val])
        currentCounts := patchCounts Q currentCounts (oldInside \ localAnswer) (localAnswer \ oldInside)
        currentOld := patchVector currentOld region (fun r => decide (r ∈ localAnswer))
        currentAvailable := patchVector currentAvailable (removed ∪ added) (fun r => decide (r ∈ added))
  let result := [("initial_answer", toJson ((oldAnswer.sort (· ≤ ·)).map Fin.val)),
    ("queries", Json.arr answers)]
  return Json.mkObj (match setupCharge with
    | some fee => ("setup_charge", toJson fee)::result
    | none => result)

end RAFQueryCompilation.Runtime

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--benchmark", path] =>
    let raw ← IO.FS.readFile path
    match Lean.Json.parse raw >>= Lean.Json.getArr? with
    | .error message => IO.eprintln message; pure 1
    | .ok packets =>
      for packet in packets do
        let .ok text := packet.getStr? | throw (IO.userError "expected raw packet string")
        let started ← IO.monoNanosNow
        let result := Lean.Json.parse text >>= RAFQueryCompilation.Runtime.runPacket
        let encoded := match result with
          | .ok answer => answer.compress
          | .error message => Lean.Json.compress (Lean.Json.mkObj [("error", Lean.toJson message)])
        -- Force serialization before taking the end timestamp.
        let bytes := encoded.utf8ByteSize
        if bytes == 0 then throw (IO.userError "empty result")
        let finished ← IO.monoNanosNow
        IO.println (Lean.Json.mkObj [("elapsed_ns", Lean.toJson (finished - started)),
          ("result", Lean.toJson encoded), ("output_bytes", Lean.toJson bytes)]).compress
      pure 0
  | [path] =>
    let raw ← IO.FS.readFile path
    match Lean.Json.parse raw >>= RAFQueryCompilation.Runtime.runPacket with
    | .ok answer => IO.println answer.compress; pure 0
    | .error message =>
      IO.eprintln message
      pure 1
  | _ => IO.eprintln "usage: RAF checker packet.json"; pure 1

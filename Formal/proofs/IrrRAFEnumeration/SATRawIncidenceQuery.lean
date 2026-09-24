import proofs.IrrRAFEnumeration.SATRawIncidenceMissing

namespace IrrRAFEnumeration.SATSource

open Complexity SAT Complexity.TM

def incidenceCNFMatch (sign : Bool) (v : Nat) : CNF → Nat → Bool
  | [], _ => false
  | c :: _, 0 => incidenceClauseMatch sign v c
  | _ :: cs, j+1 => incidenceCNFMatch sign v cs j

theorem incidenceCNFMatch_append (sign : Bool) (v : Nat) (pre post : CNF) (c : Clause) :
    incidenceCNFMatch sign v (pre ++ c :: post) pre.length = incidenceClauseMatch sign v c := by
  induction pre with
  | nil => rfl
  | cons a pre ih => simpa [incidenceCNFMatch] using ih

theorem incidenceCNFMatch_missing (sign : Bool) (v j : Nat) (φ : CNF) (hj : φ.length ≤ j) :
    incidenceCNFMatch sign v φ j = false := by
  induction φ generalizing j with
  | nil => rfl
  | cons c cs ih =>
    cases j with
    | zero => simp at hj
    | succ j => exact ih j (by simpa using hj)

theorem incidence_index_split (φ : CNF) (j : Nat) (hj : j < φ.length) :
    ∃ pre c post, φ = pre ++ c :: post ∧ pre.length = j := by
  induction φ generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    cases j with
    | zero => exact ⟨[],c,cs,rfl,rfl⟩
    | succ j =>
      obtain ⟨pre,a,post,he,hl⟩ := ih j (by simpa using hj)
      exact ⟨c::pre,a,post,by simp [he],by simp [hl]⟩

/-- One uniform runtime-index contract, including absent clauses. All heads
needed by the restoration phase are bounded by the explicit source size. -/
theorem incidence_query_run (sign : Bool) (v j : Nat) (φ : CNF)
    (inp out : Tape) (ys : List Bool) (hin : inp.HasBinarySuffix φ.encode)
    (hout : OutAcc ys out) :
    ∃ inp' out' t h, t ≤ 2*φ.encode.length+3 ∧ 1 ≤ h ∧ h ≤ φ.length+1 ∧
      (rawIncidenceTM sign).reachesIn t
        (incidenceCfg (incidenceScan false) inp (regTape j) (regTape v) out)
        (incidenceCfg incidenceHalt inp' ⟨h,regCells j⟩ (regTape v) out') ∧
      OutAcc (ys ++ [incidenceCNFMatch sign v φ j]) out' ∧ Parked inp' ∧
      inp'.cells = inp.cells ∧ inp'.head ≤ inp.head+φ.encode.length := by
  by_cases hj : j < φ.length
  · obtain ⟨pre,c,post,hφ,hpre⟩ := incidence_index_split φ j hj
    subst φ
    subst j
    obtain ⟨inp',out',t,ht,hr,ho,hs,hc,hh⟩ := incidence_located_clause_run sign v pre post c
      inp out ys hin hout
    refine ⟨inp',out',t,pre.length+1,ht,by omega,by simp,hr,?_,⟨hs.1,hs.2.2.2⟩,hc,?_⟩
    · simpa only [incidenceCNFMatch_append] using ho
    · simp only [CNF.encode_append,CNF.encode_cons,List.length_append,List.length_cons,List.length_nil]
      omega
  · have hge : φ.length ≤ j := by omega
    obtain ⟨inp',out',hr,ho,hs,hc,hh⟩ := incidence_missing_clause_run sign v j φ inp out ys hin hge hout
    refine ⟨inp',out',φ.encode.length+2,φ.length+1,by omega,by omega,le_rfl,
      hr,?_,⟨hs.1,hs.2.2.2⟩,hc,by omega⟩
    simpa only [incidenceCNFMatch_missing sign v j φ hge] using ho

end IrrRAFEnumeration.SATSource

import proofs.IrrRAFEnumeration.CompletionPositiveRound

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- A prepared-state emitter's output length is bounded by its actual runtime,
because its output head advances by at most one position per transition. -/
theorem emitted_length_le {n : Nat} (M : TM n) (inp inp' : Tape)
    (work work' : Fin n → Tape) (xs : List Bool) (b : Nat)
    (h : M.HoareTime (EmitPred inp work []) (EmitPred inp' work' xs) b) : xs.length ≤ b := by
  obtain ⟨c,t,ht,hr,hh,ha,hw,ho⟩ := h inp work (accumulatorTape [])
    ⟨rfl,rfl,accumulatorTape_outAcc []⟩
  have hb := M.output_head_reachesIn_bound hr
  have he := ho.1
  change c.output.head ≤ 1+t at hb
  omega

def blockerSizeBound (r : Nat) := r*(10*r+58)+r+6

theorem blockerClause_encode_length_le {r : Nat} (U : Finset (Fin r)) :
    (SAT.CNF.encode [blockerClause U]).length ≤ blockerSizeBound r := by
  have h := selectedClauseTM_correct false (parkedInput (containerMask U)) 1 0 r []
    (parkedInput_parked _) rfl rfl
  rw [containerMask_blocker U] at h
  simp only [List.nil_append,Nat.zero_add] at h
  have ht : r*(5*1+5*0+10*r+53)+r+6 = blockerSizeBound r := by
    unfold blockerSizeBound
    ring
  rw [ht] at h
  exact emitted_length_le _ _ _ _ _ _ _ h

theorem outputBlockers_encode_length_le {r : Nat} (G : List (Finset (Fin r))) :
    (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length ≤ G.length*blockerSizeBound r := by
  induction G with
  | nil => simp [PositiveCompletionCNF.outputBlockers]
  | cons I G ih =>
    have he : PositiveCompletionCNF.outputBlockers (I::G) =
        [blockerClause I]++PositiveCompletionCNF.outputBlockers G := rfl
    rw [he,SAT.CNF.encode_append,List.length_append]
    have hi := blockerClause_encode_length_le I
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem dynamicQuery_encode_length_le {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)).length ≤
      dynamicQueryTime (SAT.CNF.encode (assembledBase Q C)).length
        (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length r := by
  exact emitted_length_le _ _ _ _ _ _ _
    (dynamicQueryTM_correct Q C G U (parkedInput []) (parkedInput_parked []))

end IrrRAFEnumeration.CompletionQuery

import proofs.IrrRAFEnumeration.CompletionOuterFamily

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- The actual SAT-driven outer loop reaches a complete duplicate-free family.
The only remaining cost premise is a uniform bound on generated SAT calls.
Initialization of the prepared persistent state is a separate obligation. -/
theorem enumLoopTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (a : Nat)
    (hcost : ∀ G, GoodFamily (irrRAFFamily Q C) G →
      ∀ U, fullQueryCost (k := k) q T Q C G U ≤ a)
    (inp : Tape) (hp : Parked inp) :
    (enumLoopTM q M).HoareTime
      (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
        (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) [])
      (fun x w out => ∃ G : List (Finset (Fin r)),
        GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
        EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C))
          (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)) (storedMasks G) 0 G.length) [] x w out)
      (((irrRAFFamily Q C).card+1)*(a+roundTimeBound r (irrRAFFamily Q C).card a+2)) := by
  classical
  let F := irrRAFFamily Q C
  let state := fun (G : List (Finset (Fin r))) (bit : Nat) =>
    EmitPred inp (enumFlagWork k (Finset.univ : Finset (Fin r))
      (SAT.CNF.encode (assembledBase Q C))
      (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)) (storedMasks G) 0 G.length bit) []
  let inv := fun m x w out => ∃ G, GoodFamily F G ∧ G.length+m=F.card ∧ state G 0 x w out
  let mid := fun m x w out => ∃ G, GoodFamily F G ∧ G.length+(m+1)=F.card ∧
    PositiveCompletion.Available (IsRAF Q C) G.toFinset Finset.univ ∧ state G 1 x w out
  let post := fun x w out => ∃ G, GoodFamily F G ∧ G.toFinset=F ∧ state G 0 x w out
  have hpark : ∀ m x w out, inv m x w out → Parked x ∧ (∀ i, Parked (w i)) ∧ Parked out := by
    rintro m x w out ⟨G,_,_,hx,hw,ho⟩
    subst x
    subst w
    exact ⟨hp,enumFlagWork_parked _ _ _ _ _ _ _ _,ho.parked⟩
  have hquery : ∀ m, (enumCompletionTM q M).HoareTime (inv m)
      (fun x w out => Parked x ∧ (∀ i, Parked (w i)) ∧ Parked out ∧
        (((w (enumFlag k)).read ≠ Γ.one ∧ post x w out) ∨
          ((w (enumFlag k)).read = Γ.one ∧ ∃ j < m, mid j x w out))) a := by
    rintro m x w out ⟨G,hG,hlen,hpre⟩
    have hc := (enumCompletionTM_correct q Q C G Finset.univ 0 M T hM hq inp hp).mono_bound
      (hcost G hG Finset.univ)
    obtain ⟨c,t,ht,hr,hh,bit,hbit,hans,hx,hw,ho⟩ := hc x w out hpre
    have hvalid : ∀ I ∈ G.toFinset, Minimal (IsRAF Q C) I := by
      intro I hi
      exact (mem_irrRAFFamily Q C I).mp (hG.2 hi)
    have hf : (c.work (enumFlag k)).read = (regTape bit).read := by
      rw [hw,enumFlagWork_flag]
    refine ⟨c,t,ht,hr,hh,?_,?_,ho.parked,?_⟩
    · rw [hx]
      exact hp
    · rw [hw]
      exact enumFlagWork_parked _ _ _ _ _ _ _ _
    · have hb : bit = 0 ∨ bit = 1 := by omega
      rcases hb with rfl | rfl
      · left
        refine ⟨?_,G,hG,?_,hx,hw,ho⟩
        · rw [hf]
          simp [regTape,regCells,Tape.read]
        · apply Finset.Subset.antisymm hG.2
          intro I hi
          by_contra hn
          have ha := PositiveCompletion.available_univ_iff_missing hvalid |>.mpr
            ⟨I,(mem_irrRAFFamily Q C I).mp hi,hn⟩
          have := hans.mpr ha
          omega
      · right
        have hav := hans.mp rfl
        obtain ⟨I,hI,hnew⟩ := (PositiveCompletion.available_univ_iff_missing hvalid).mp hav
        have hlen' := goodFamily_length_le
          (goodFamily_append hG ((mem_irrRAFFamily Q C I).mpr hI) hnew)
        simp only [List.length_append,List.length_singleton] at hlen'
        refine ⟨?_,m-1,by omega,G,hG,by omega,hav,hx,hw,ho⟩
        simpa [regTape,regCells,Tape.read] using hf
  have hbody : ∀ m, (positiveRoundTM q M).HoareTime (mid m) (inv m)
      (roundTimeBound r F.card a) := by
    rintro m x w out ⟨G,hG,hlen,hav,hpre⟩
    obtain ⟨V,hV,hnew,h⟩ := positiveRound_uniform q Q C G F.card a
      (goodFamily_length_le hG) hav M T hM hq (hcost G hG) inp hp
    obtain ⟨c,t,ht,hr,hh,hpost⟩ := h x w out hpre
    refine ⟨c,t,ht,hr,hh,G++[V],
      goodFamily_append hG ((mem_irrRAFFamily Q C V).mpr hV) hnew,?_,hpost⟩
    simp only [List.length_append,List.length_singleton]
    omega
  have h := workWhileTM_correct (enumCompletionTM q M) (positiveRoundTM q M) (enumFlag k)
    inv mid post a (roundTimeBound r F.card a) hpark hquery hbody F.card
  apply h.weaken_pre
  intro x w out hpre
  refine ⟨[],?_,by simp,?_⟩
  · simp [GoodFamily]
  · simpa [state,PositiveCompletionCNF.outputBlockers,storedMasks] using hpre

end IrrRAFEnumeration.CompletionQuery

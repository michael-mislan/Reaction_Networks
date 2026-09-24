import proofs.IrrRAFEnumeration.CompletionMinimizeSemantics

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PolynomialClockSetup

/-- Actual SAT-driven minimization. The deliberately conservative bound sums only
the r generated trial costs, never all possible containers or all SAT witnesses. -/
theorem satMinimize_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (hU : PositiveCompletion.Available (IsRAF Q C) G.toFinset U)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (inp : Tape) (hp : Parked inp) :
    let base := SAT.CNF.encode (assembledBase Q C)
    let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
    ∃ b : Nat,
      (∃ cost : Fin r → Nat,
        (∀ i, ∃ V : Finset (Fin r), cost i = completionCallTime k q T r base.length blocks.length
          (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
            PositiveCompletionCNF.containerExclusions V)).length) ∧
        b = r*((∑ i, cost i)+12*r+33)+(r+2)) ∧
      (minimizeTM (restoredCompletionTM q M)).HoareTime
        (EmitPred inp (minimizeWork k U base blocks 0) [])
        (fun a w out => ∃ V, Minimal (IsRAF Q C) V ∧ V ∉ G.toFinset ∧
          EmitPred inp (minimizeWork k V base blocks r) [] a w out) b := by
  classical
  dsimp only
  let P := PositiveCompletion.Available (IsRAF Q C) G.toFinset
  let base := SAT.CNF.encode (assembledBase Q C)
  let blocks := SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)
  let V := fun i : Fin r => (deletionStates P U i.val).erase i
  let cost := fun i : Fin r => completionCallTime k q T r base.length blocks.length
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions (V i))).length
  let b := ∑ i, cost i
  have hc : ∀ i (hi : i < r), (restoredCompletionTM q M).HoareTime
      (EmitPred inp (completionWork k ((deletionStates P U i).erase ⟨i,hi⟩) base blocks) [])
      (completionResult k ((deletionStates P U i).erase ⟨i,hi⟩) base blocks inp
        (P ((deletionStates P U i).erase ⟨i,hi⟩))) b := by
    intro i hi
    have h := reusableCompletionTM_correct q Q C G (V ⟨i,hi⟩) M T hM hq inp hp
    have hb : cost ⟨i,hi⟩ ≤ b := Finset.single_le_sum
      (fun j _ => Nat.zero_le (cost j)) (Finset.mem_univ (⟨i,hi⟩ : Fin r))
    exact h.mono_bound hb
  have h := minimizeTM_correct (restoredCompletionTM q M) P
    (fun _ _ hs => PositiveCompletion.available_mono hs) U hU base blocks inp hp b hc
  refine ⟨_,⟨cost,fun i => ⟨V i,rfl⟩,rfl⟩,?_⟩
  apply h.strengthen_post
  rintro a w out ⟨S,hS,hpost⟩
  obtain ⟨hmin,havoid⟩ := PositiveCompletion.minimal_available hS
  exact ⟨S,hmin,fun hm => havoid S hm Finset.Subset.rfl,hpost⟩

end IrrRAFEnumeration.CompletionQuery

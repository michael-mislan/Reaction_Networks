import proofs.IrrRAFEnumeration.CompletionOuterTermination

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def GoodFamily {r : Nat} (F : Finset (Finset (Fin r))) (G : List (Finset (Fin r))) :=
  G.Nodup ∧ G.toFinset ⊆ F

theorem goodFamily_length_le {r : Nat} {F : Finset (Finset (Fin r))}
    {G : List (Finset (Fin r))} (h : GoodFamily F G) : G.length ≤ F.card := by
  rw [← List.toFinset_card_of_nodup h.1]
  exact Finset.card_le_card h.2

theorem goodFamily_complete {r : Nat} {F : Finset (Finset (Fin r))}
    {G : List (Finset (Fin r))} (h : GoodFamily F G) (hc : G.length = F.card) :
    G.toFinset = F := by
  exact Finset.eq_of_subset_of_card_le h.2 (by rw [List.toFinset_card_of_nodup h.1,hc])

theorem goodFamily_append {r : Nat} {F : Finset (Finset (Fin r))}
    {G : List (Finset (Fin r))} (h : GoodFamily F G) {V : Finset (Fin r)}
    (hv : V ∈ F) (hn : V ∉ G.toFinset) : GoodFamily F (G++[V]) := by
  constructor
  · apply List.nodup_append.mpr
    refine ⟨h.1,by simp,?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro he
    subst a
    exact hn (List.mem_toFinset.mpr ha)
  · intro I hi
    simp only [List.mem_toFinset,List.mem_append,List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact h.2 (List.mem_toFinset.mpr hi)
    · exact hv

def fullQueryCost {d r k : Nat} (q : Polynomial Nat) (T : Nat → Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :=
  completionCallTime k q T r (SAT.CNF.encode (assembledBase Q C)).length
    (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)).length
    (SAT.CNF.encode (assembledBase Q C ++ PositiveCompletionCNF.outputBlockers G ++
      PositiveCompletionCNF.containerExclusions U)).length

def roundTimeBound (r K a : Nat) :=
  6+1+(r*(r*a+12*r+33)+(r+2)+1+
    (2*r+6+blockerCommitTime r (K*blockerSizeBound r) (blockerSizeBound r)+1+2*K+4))+
    1+(7*r*r+20*r+12)

/-- A uniform bound on actual generated calls bounds the whole concrete round.
The family and support witnesses are not enumerated to compute this bound. -/
theorem positiveRound_uniform {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (K a : Nat) (hK : G.length ≤ K)
    (hU : PositiveCompletion.Available (IsRAF Q C) G.toFinset Finset.univ)
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2)
    (hc : ∀ U, fullQueryCost (k := k) q T Q C G U ≤ a)
    (inp : Tape) (hp : Parked inp) :
    ∃ V : Finset (Fin r), Minimal (IsRAF Q C) V ∧ V ∉ G.toFinset ∧
      (positiveRoundTM q M).HoareTime
        (EmitPred inp (enumFlagWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G))
          (storedMasks G) 0 G.length 1) [])
        (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C)) (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers (G++[V])))
          (storedMasks (G++[V])) 0 (G++[V]).length) []) (roundTimeBound r K a) := by
  obtain ⟨cost,V,hcost,hv,hn,hr⟩ := positiveRoundTM_correct q Q C G hU M T hM hq inp hp
  refine ⟨V,hv,hn,hr.mono_bound ?_⟩
  have hs : (∑ i, cost i) ≤ r*a := by
    calc
      (∑ i, cost i) ≤ ∑ _i : Fin r, a := Finset.sum_le_sum (fun i _ => by
        obtain ⟨U,he⟩ := hcost i
        rw [he]
        exact hc U)
      _ = r*a := by simp
  have hb := outputBlockers_encode_length_le G
  have hb' := Nat.mul_le_mul_right (blockerSizeBound r) hK
  have hv' := blockerClause_encode_length_le V
  have hm := Nat.mul_le_mul_left r (show (∑ i, cost i)+12*r+33 ≤ r*a+12*r+33 by omega)
  unfold roundTimeBound blockerCommitTime
  omega

end IrrRAFEnumeration.CompletionQuery

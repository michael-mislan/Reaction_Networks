import proofs.IrrRAFEnumeration.CompletionEnumerationLoop
import proofs.IrrRAFEnumeration.CompletionFinish

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

theorem storedMasks_length {r : Nat} (G : List (Finset (Fin r))) :
    (storedMasks G).length = r*G.length := by
  induction G with
  | nil => simp [storedMasks]
  | cons I G ih =>
    change (containerMask I ++ storedMasks G).length = r*(G.length+1)
    rw [List.length_append,ih]
    simp [containerMask,Nat.mul_add,Nat.add_comm]

def preparedEnumerationTM {k : Nat} (q : Polynomial Nat) (M : TM k) :=
  seqTM (enumLoopTM q M) (finishTM k)

/-- Complete actual enumeration and output from the prepared initial buffers.
This does not assume the final family as input or enumerate SAT witnesses. -/
theorem preparedEnumerationTM_correct {d r k : Nat} (q : Polynomial Nat)
    (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (M : TM k) (T : Nat → Nat) (hM : M.DecidesInTime SAT.language T)
    (hq : ∀ L, q.eval L = T L+L+2) (a : Nat)
    (hcost : ∀ G, GoodFamily (irrRAFFamily Q C) G →
      ∀ U, fullQueryCost (k := k) q T Q C G U ≤ a)
    (inp : Tape) (hp : Parked inp) :
    (preparedEnumerationTM q M).HoareTime
      (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
        (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) [])
      (fun x _ out => x = inp ∧ ∃ G : List (Finset (Fin r)),
        GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
        OutAcc (outputBits (Equiv.refl (Fin r)) G) out)
      (((irrRAFFamily Q C).card+1)*(a+roundTimeBound r (irrRAFFamily Q C).card a+2)+1+
        (3*(r*(irrRAFFamily Q C).card)+4*(irrRAFFamily Q C).card+14)) := by
  have hloop := enumLoopTM_correct q Q C M T hM hq a hcost inp hp
  apply seqTM_hoareTime _ _ (mid' := fun x w out => ∃ G : List (Finset (Fin r)),
    GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
    EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
      (SAT.CNF.encode (assembledBase Q C))
      (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)) (storedMasks G) 0 G.length) [] x w out) hloop
  · rintro x w out ⟨G,hG,he,hx,hw,ho⟩
    subst x
    subst w
    exact ⟨G,hG,he,emitPred_transition hp (enumWork_parked _ _ _ _ _ _ _) [] _ _ _ ⟨rfl,rfl,ho⟩⟩
  · rintro x w out ⟨G,hG,he,hpre⟩
    have hlen : G.length = (irrRAFFamily Q C).card := by
      rw [← List.toFinset_card_of_nodup hG.1,he]
    have h := finishTM_correct k (Finset.univ : Finset (Fin r))
      (SAT.CNF.encode (assembledBase Q C))
      (SAT.CNF.encode (PositiveCompletionCNF.outputBlockers G)) G 0 inp hp
    have hb : 3*(storedMasks G).length+4*G.length+14 =
        3*(r*(irrRAFFamily Q C).card)+4*(irrRAFFamily Q C).card+14 := by
      rw [storedMasks_length,hlen]
    rw [hb] at h
    obtain ⟨c,t,ht,hr,hh,hx,_,ho⟩ := h x w out hpre
    exact ⟨c,t,ht,hr,hh,hx,G,hG,he,ho⟩

end IrrRAFEnumeration.CompletionQuery

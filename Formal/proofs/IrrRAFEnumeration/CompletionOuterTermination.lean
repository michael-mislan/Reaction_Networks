import proofs.IrrRAFEnumeration.CompletionOuterControl

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- A proof-only decreasing index bounds the actual work-flag loop. The test
chooses the physical branch; the index is not an input to the machine. -/
theorem workWhileTM_correct {n : Nat} (test body : TM n) (flag : Fin n)
    (inv mid : Nat → TM.TapePred n) (post : TM.TapePred n) (a b : Nat)
    (hpark : ∀ m inp work out, inv m inp work out →
      Parked inp ∧ (∀ i, Parked (work i)) ∧ Parked out)
    (hquery : ∀ m, test.HoareTime (inv m)
      (fun inp work out => Parked inp ∧ (∀ i, Parked (work i)) ∧ Parked out ∧
        (((work flag).read ≠ Γ.one ∧ post inp work out) ∨
          ((work flag).read = Γ.one ∧ ∃ j < m, mid j inp work out))) a)
    (hbody : ∀ m, body.HoareTime (mid m) (inv m) b) (m : Nat) :
    (workWhileTM test body flag).HoareTime (inv m) post ((m+1)*(a+b+2)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro inp work out hpre
    obtain ⟨⟨s,inp1,work1,out1⟩,t,ht,hr,hh,hp,hw,ho,hs⟩ := hquery m inp work out hpre
    change s = test.qhalt at hh
    subst s
    have rt := reachesIn_map (whileTestCfg test body flag)
      (fun _ _ h => whileTest_step test body flag h) hr
    have he := whileTest_exit test body flag inp1 work1 out1 hp hw ho
    rcases hs with ⟨hf,hpost⟩ | ⟨hf,j,hjm,hmid⟩
    · rw [if_neg hf] at he
      refine ⟨⟨.inr (.inr ()),inp1,work1,out1⟩,t+1,?_,
        reachesIn_trans _ rt (.step he .zero),rfl,hpost⟩
      have hm : 1*(a+b+2) ≤ (m+1)*(a+b+2) := Nat.mul_le_mul_right _ (by omega)
      omega
    · rw [if_pos hf] at he
      obtain ⟨⟨s,inp2,work2,out2⟩,u,hu,hb,hh,hinv⟩ := hbody j inp1 work1 out1 hmid
      change s = body.qhalt at hh
      subst s
      obtain ⟨hp2,hw2,ho2⟩ := hpark j inp2 work2 out2 hinv
      have rb := reachesIn_map (whileBodyCfg test body flag)
        (fun _ _ h => whileBody_step test body flag h) hb
      have hx := whileBody_exit test body flag inp2 work2 out2 hp2 hw2 ho2
      obtain ⟨c,v,hv,ri,hhalt,hpost⟩ := ih j hjm inp2 work2 out2 hinv
      refine ⟨c,t+(u+(v+1)+1),?_,
        reachesIn_trans _ rt (.step he (reachesIn_trans _ rb (.step hx ri))),hhalt,hpost⟩
      have hm : (j+1)*(a+b+2) ≤ m*(a+b+2) := Nat.mul_le_mul_right _ (by omega)
      have heq : (m+1)*(a+b+2) = m*(a+b+2)+(a+b+2) := by ring
      omega

end IrrRAFEnumeration.CompletionQuery

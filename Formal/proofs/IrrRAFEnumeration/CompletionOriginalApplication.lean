import proofs.IrrRAFEnumeration.CompletionConditionalEnumeration

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

/-- The actual enumeration contract restricted to the identifiers physically encoded. -/
def FinEnumerates {n : Nat} (E : TM n) (p : Polynomial Nat) : Prop :=
  ∀ (d r : Nat) (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r))
    [DecidableRel C],
    ∃ (rows : List (Finset (Fin r))) (c : Cfg n E.Q) (t : Nat),
      rows.Nodup ∧ rows.toFinset = irrRAFFamily Q C ∧
      t ≤ p.eval ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+
        (outputBits (Equiv.refl _) rows).length) ∧
      E.reachesIn t (E.initCfg (inputBits Q C (Equiv.refl _) (Equiv.refl _))) c ∧
      E.halted c ∧ c.output.HasOutput (outputBits (Equiv.refl _) rows)

abbrev enumTapes (k : Nat) := (((bufferedCount k+1)+1)+1)+1

/-- The exact prefix obligation; all dimensions and chemistry are computed from input. -/
def InitializesEnumeration (k m : Nat) (I : TM (enumTapes k+m))
    (p : Polynomial Nat) : Prop :=
  ∀ (d r : Nat) (Q : CRS (Fin d) (Fin r)) (C : Catalysis (Fin d) (Fin r))
    [DecidableRel C],
    I.HoareTime
      (fun inp work out =>
        inp = Tape.init ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).map Γ.ofBool) ∧
        (∀ i, work i = Tape.init []) ∧ out = Tape.init [])
      (fun inp work out => ∃ extra : Fin (enumTapes k+m) → Tape,
        (∀ i, Parked (extra i)) ∧
        EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (frameWork (m := m) (enumWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) extra) [] inp work out)
      (p.eval (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length)

/-- Lifting preserves arbitrary postconditions on the original tapes and exact time. -/
theorem lift_enum_post {n : Nat} (E : TM n) (m : Nat) (inp : Tape)
    (work : Fin n → Tape) (P : TM.TapePred n) (b : Nat)
    (extra : Fin (n+m) → Tape) (he : ∀ i, Parked (extra i))
    (h : E.HoareTime (EmitPred inp work []) P b) :
    (E.liftTM m).HoareTime
      (EmitPred inp (frameWork (m := m) work extra) [])
      (fun a _ out => ∃ w, P a w out) b := by
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  obtain ⟨c,t,ht,hr,hh,hpost⟩ := h inp work out ⟨rfl,rfl,ho⟩
  exact ⟨frameCfg E m extra c,t,ht,
    liftTM_reaches_frame E m extra (fun i _ => he i) hr,
    hh,c.work,hpost⟩

/-- Consumes precisely a costed physical prefix and the existing prepared theorem. -/
theorem finEnumerates_of_initializer {k m : Nat} (I : TM (enumTapes k+m))
    (p₀ : Polynomial Nat) (hI : InitializesEnumeration k m I p₀)
    (E : TM (enumTapes k)) (p₁ : Polynomial Nat)
    (hE : ∀ (d r : Nat) (Q : CRS (Fin d) (Fin r))
      (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (inp : Tape), Parked inp →
      E.HoareTime
        (EmitPred inp (enumWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) [])
        (fun x _ out => x = inp ∧ ∃ G : List (Finset (Fin r)),
          GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
          OutAcc (outputBits (Equiv.refl (Fin r)) G) out)
        (p₁.eval ((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+
          fixedWidthOutputLength r (irrRAFFamily Q C).card))) :
    FinEnumerates (seqTM I (E.liftTM m)) (p₀+p₁+1) := by
  intro d r Q C _
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  have h := seqTM_hoareTime I (E.liftTM m) (hI d r Q C)
    (post := fun a _ out => a = parkedInput z ∧ ∃ G : List (Finset (Fin r)),
      GoodFamily (irrRAFFamily Q C) G ∧ G.toFinset = irrRAFFamily Q C ∧
        OutAcc (outputBits (Equiv.refl (Fin r)) G) out)
    (mid' :=
    fun a w out => ∃ extra : Fin (enumTapes k+m) → Tape,
      (∀ i, Parked (extra i)) ∧
      EmitPred (parkedInput z) (frameWork (m := m)
        (enumWork k (Finset.univ : Finset (Fin r))
          (SAT.CNF.encode (assembledBase Q C)) [] [] 0 0) extra) [] a w out)
    (by
      rintro a w out ⟨extra,he,hpre⟩
      refine ⟨extra,he,?_⟩
      apply emitPred_transition (parkedInput_parked z) _ [] _ _ _ hpre
      intro i
      unfold frameWork
      split
      · exact enumWork_parked _ _ _ _ _ _ _ _
      · exact he i)
    (by
      rintro a w out ⟨extra,he,hpre⟩
      obtain ⟨c,t,ht,hr,hh,_,hpost⟩ := lift_enum_post E m (parkedInput z) _ _ _ extra he
        (hE d r Q C (parkedInput z) (parkedInput_parked z)) a w out hpre
      exact ⟨c,t,ht,hr,hh,hpost⟩)
  obtain ⟨c,t,ht,hr,hh,_,G,hG,hfamily,ho⟩ := h
    (Tape.init (z.map Γ.ofBool)) (fun _ => Tape.init []) (Tape.init [])
    ⟨rfl,fun _ => rfl,rfl⟩
  have hlen : G.length = (irrRAFFamily Q C).card := by
    rw [← hfamily,List.toFinset_card_of_nodup hG.1]
  refine ⟨G,c,t,hG.1,hfamily,?_,hr,hh,ho.hasOutput⟩
  rw [outputBits_length,hlen]
  have hm := polynomial_eval_mono_nat p₀
    (Nat.le_add_right z.length (fixedWidthOutputLength r (irrRAFFamily Q C).card))
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  dsimp [z] at hm
  omega

/-- The remaining transport is explicitly a CRS-identifier interpretation theorem. -/
theorem outputPolynomialEnumeration_of_initializer
    (hPNP : Complexity.P = Complexity.NP)
    (hinit : ∀ k, ∃ (m : Nat) (I : TM (enumTapes k+m)) (p : Polynomial Nat),
      InitializesEnumeration k m I p)
    (htransport : ∀ n (E : TM n) p, FinEnumerates E p → Enumerates E p) :
    OutputPolynomialEnumeration := by
  obtain ⟨k,E,p,hE⟩ := preparedEnumeration_of_P_eq_NP hPNP
  obtain ⟨m,I,q,hI⟩ := hinit k
  exact ⟨_,seqTM I (E.liftTM m),q+p+1,
    htransport _ _ _ (finEnumerates_of_initializer I q hI E p hE)⟩

end IrrRAFEnumeration.CompletionQuery

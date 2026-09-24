import proofs.IrrRAFEnumeration.CompletionInitialRegisters

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

theorem enumTapes_ge_six (k : Nat) : 6 ≤ enumTapes k := by
  unfold enumTapes bufferedCount
  omega

def initialCopiedWork (k d r : Nat) (base : List Bool) :=
  Function.update (initialBaseWork (enumTapes k) d r base)
    (initialBaseDest (enumTapes k) (enumTapes_ge_six k)) (parkedInput base)

theorem initialCopiedWork_parked (k d r : Nat) (base : List Bool) :
    ∀ i, Parked (initialCopiedWork k d r base i) := by
  intro i
  unfold initialCopiedWork
  by_cases hi : i = initialBaseDest (enumTapes k) (enumTapes_ge_six k)
  · subst i; simpa using parkedInput_parked base
  · simpa [Function.update_of_ne hi] using initialBaseWork_parked (enumTapes k) d r base i

theorem initialCopiedWork_prefix (k d r : Nat) (base : List Bool)
    (i : Fin (enumTapes k+24)) (hi : i.val < enumTapes k) :
    initialCopiedWork k d r base i =
      if i.val = 5 then parkedInput base else regTape 0 := by
  simp only [initialCopiedWork,Function.update_apply,Fin.ext_iff,initialBaseDest]
  rw [initialBaseWork_prefix _ _ _ _ i hi]

theorem initialCopiedWork_count (k d r : Nat) (base : List Bool) :
    initialCopiedWork k d r base (initCountSource k) = regTape r := by
  have hne : initCountSource k ≠ initialBaseDest (enumTapes k) (enumTapes_ge_six k) := by
    intro h
    have he := congrArg Fin.val h
    dsimp [initCountSource,initialBaseDest] at he
    have := enumTapes_ge_six k
    omega
  unfold initialCopiedWork
  rw [Function.update_of_ne hne]
  simp [initialBaseWork,initCountSource,placedClockWork,placeWorkInMiddle,
    placeWorkCoord,frameWork,baseRegWork]
  rw [baseRunState_bank d r 6 (13 : Fin 23) (by decide)]
  rfl

theorem initialFinalWork_parked (k d r : Nat) (base : List Bool) :
    ∀ i, Parked (initialRegisterWork k r (initialCopiedWork k d r base) i) := by
  exact updateReg_parked _
    (updateReg_parked _ (updateReg_parked _
      (updateReg_parked _ (initialCopiedWork_parked k d r base) _ _) _ _) _ _) _ _

/-- All prepared fields agree; the unobserved extra bank stays parked. -/
theorem initialFinalWork_eq (k d r : Nat) (base : List Bool) :
    initialRegisterWork k r (initialCopiedWork k d r base) =
      frameWork (m := 24) (enumWork k (Finset.univ : Finset (Fin r)) base [] [] 0 0)
        (initialRegisterWork k r (initialCopiedWork k d r base)) := by
  funext i
  by_cases hi : i.val < enumTapes k
  · simp only [frameWork,hi,↓reduceDIte]
    rw [enumWork_initial_cell]
    simp only [initialRegisterWork,Function.update_apply,Fin.ext_iff,
      initSmall,initFuel]
    rw [initialCopiedWork_prefix k d r base i hi]
    have hf : 5 < bufferedCount k+1 := by unfold bufferedCount; omega
    split_ifs <;> first | rfl | omega
  · simp [frameWork,hi]

def originalInitializerTM (k : Nat) : TM (enumTapes k+24) :=
  seqTM (initialBaseTM (enumTapes k) (enumTapes_ge_six k)) (initialRegisterTM k)

noncomputable def originalInitializerPolynomial : Polynomial Nat :=
  50000000*(Polynomial.X+1)^6+6*Polynomial.X*Polynomial.X+21*Polynomial.X+54

/-- One fixed input prefix supplies every field of the prepared enumerator. -/
theorem originalInitializer_correct (k : Nat) :
    InitializesEnumeration k 24 (originalInitializerTM k) originalInitializerPolynomial := by
  intro d r Q C _
  let z := inputBits Q C (Equiv.refl _) (Equiv.refl _)
  let base := SAT.CNF.encode (assembledBase Q C)
  let W := initialCopiedWork k d r base
  have hp := parkedInput_parked z
  have hw := initialCopiedWork_parked k d r base
  have hsmall (i : Fin 7) (hi : i.val ≠ 5) : W (initSmall k i) = regTape 0 := by
    have hb : (initSmall k i).val < enumTapes k := by
      change i.val < enumTapes k
      have := i.isLt
      unfold enumTapes bufferedCount
      omega
    simpa [initSmall,hi] using initialCopiedWork_prefix k d r base (initSmall k i) hb
  have hf : W (initFuel k) = regTape 0 := by
    have hb : (initFuel k).val < enumTapes k := by
      change bufferedCount k+1 < enumTapes k
      unfold enumTapes
      omega
    have hne : (initFuel k).val ≠ 5 := by
      change bufferedCount k+1 ≠ 5
      unfold bufferedCount
      omega
    simpa [hne] using initialCopiedWork_prefix k d r base (initFuel k) hb
  have hreg := initialRegisterTM_correct k r (parkedInput z) W hp hw
    (initialCopiedWork_count k d r base) (hsmall 0 (by decide))
    (hsmall 4 (by decide)) hf (hsmall 1 (by decide))
  have h := seqTM_hoareTime _ _
    (initialBaseTM_correct (enumTapes k) (enumTapes_ge_six k) Q C)
    (emitPred_transition hp hw []) hreg
  apply h.consequence
  · exact fun _ _ _ hpre => hpre
  · rintro inp work out ⟨hi,hw',ho⟩
    refine ⟨initialRegisterWork k r W,initialFinalWork_parked k d r base,hi,?_,ho⟩
    exact hw'.trans (initialFinalWork_eq k d r base)
  · have hr : r ≤ z.length := by simp [z,inputBits]; omega
    simp [originalInitializerPolynomial]
    change (50000000*(z.length+1)^6+16)+1+(6*r*r+21*r+37) ≤ _
    have hrr := Nat.mul_le_mul hr hr
    nlinarith

end IrrRAFEnumeration.CompletionQuery

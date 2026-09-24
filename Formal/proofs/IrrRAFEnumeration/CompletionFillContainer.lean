import proofs.IrrRAFEnumeration.CompletionFinish

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def filledContainer {r : Nat} (U : Finset (Fin r)) (i : Nat) : Finset (Fin r) :=
  U ∪ Finset.univ.filter (fun j => j.val < i)

theorem filledContainer_zero {r : Nat} (U : Finset (Fin r)) : filledContainer U 0 = U := by
  simp [filledContainer]

theorem filledContainer_all {r : Nat} (U : Finset (Fin r)) : filledContainer U r = Finset.univ := by
  ext j
  simp [filledContainer]

theorem filledContainer_step {r : Nat} (U : Finset (Fin r)) (i : Nat) (hi : i < r) :
    insert (⟨i,hi⟩ : Fin r) (filledContainer U i) = filledContainer U (i+1) := by
  ext j
  simp only [filledContainer,Finset.mem_insert,Finset.mem_union,Finset.mem_filter,
    Finset.mem_univ,true_and,Fin.ext_iff]
  by_cases hmem : j ∈ U
  · simp [hmem]
  · simp only [hmem,false_or]
    omega

def fillContainerStepTM {n : Nat} (address dst : Fin n) : TM n :=
  seqTM (editWorkTM address dst Γw.one) (incRegTM address)

def fillContainerTM {n : Nat} (fuel address dst : Fin n) : TM n :=
  forRegTM (fillContainerStepTM address dst) fuel

/-- Set every mask bit through a runtime-counted scan, preserving all other data
except the address register, which advances from zero to r. -/
theorem fillContainerTM_correct {n r : Nat} (fuel address dst : Fin n)
    (hda : dst ≠ address) (hdf : dst ≠ fuel) (haf : address ≠ fuel)
    (U : Finset (Fin r)) (inp : Tape) (work : Fin n → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (hf : work fuel = regTape r) (ha : work address = regTape 0)
    (hm : work dst = parkedInput (containerMask U)) :
    (fillContainerTM fuel address dst).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update
        (Function.update work dst (parkedInput (containerMask (Finset.univ : Finset (Fin r)))))
        address (regTape r)) ys) (r*(7*r+15)+(r+2)) := by
  let W := fun i => Function.update
    (Function.update work dst (parkedInput (containerMask (filledContainer U i)))) address (regTape i)
  have hwP : ∀ i j, Parked (W i j) := by
    intro i j
    by_cases hja : j = address
    · subst j
      simp only [W,Function.update_self]
      exact parked_regTape _
    · by_cases hjd : j = dst
      · subst j
        simp only [W,Function.update_of_ne hda,Function.update_self]
        exact parkedInput_parked _
      · simpa only [W,Function.update_of_ne hja,Function.update_of_ne hjd] using hw j
  have hbody : ∀ i, i < r → (fillContainerStepTM address dst).HoareTime
      (EmitPred inp (Function.update (W i) fuel ⟨i+2,regCells r⟩) ys)
      (EmitPred inp (Function.update (W (i+1)) fuel ⟨i+2,regCells r⟩) ys) (7*r+13) := by
    intro i hi
    let Z := Function.update (W i) fuel ⟨i+2,regCells r⟩
    have hz : ∀ j, Parked (Z j) := by
      intro j
      by_cases hj : j = fuel
      · subst j
        simpa only [Z,Function.update_self] using parked_regCells (v := r) (h := i+2) (by omega)
      · simpa only [Z,Function.update_of_ne hj] using hwP i j
    have he := editContainerTM_correct address dst hda (filledContainer U i) ⟨i,hi⟩ true
      inp Z ys hp hz
      (by simp [Z,W,Function.update_of_ne haf])
      (by simp [Z,W,Function.update_of_ne hdf,Function.update_of_ne hda])
    simp only [ite_true,filledContainer_step U i hi] at he
    let Z' := Function.update Z dst (parkedInput (containerMask (filledContainer U (i+1))))
    have hzP : ∀ j, Parked (Z' j) := by
      intro j
      by_cases hj : j = dst
      · subst j
        simp only [Z',Function.update_self]
        exact parkedInput_parked _
      · simpa only [Z',Function.update_of_ne hj] using hz j
    have hc := incRegTM_hoareTime address i inp Z' ys hp (fun j _ => hzP j)
      (by simp [Z',Z,W,Function.update_of_ne (Ne.symm hda),Function.update_of_ne haf])
    have hout : Function.update Z' address (regTape (i+1)) =
        Function.update (W (i+1)) fuel ⟨i+2,regCells r⟩ := by
      funext j
      by_cases hja : j = address
      · subst j
        simp [Z',Z,W,Function.update_of_ne haf]
      · by_cases hjd : j = dst
        · subst j
          simp [Z',Z,W,Function.update_of_ne hdf,Function.update_of_ne hda]
        · by_cases hjf : j = fuel
          · subst j
            simp [Z',Z,W,Ne.symm haf,Ne.symm hdf]
          · simp [Z',Z,W,Function.update_of_ne hja,Function.update_of_ne hjd,Function.update_of_ne hjf]
    rw [hout] at hc
    have h := seqTM_hoareTime _ _ he (emitPred_transition hp hzP ys) hc
    exact h.mono_bound (by omega)
  have h := forRegTM_hoareTime (fillContainerStepTM address dst) fuel r inp W (fun _ => ys)
    (7*r+13) hp (fun _ => by simp [W,Ne.symm haf,Ne.symm hdf,hf])
    (fun i j _ => hwP i j) hbody
  have hzero : W 0 = work := by
    simp [W,filledContainer_zero,← hm,← ha,Function.update_eq_self]
  simpa only [fillContainerTM,hzero,W,filledContainer_all] using h

end IrrRAFEnumeration.CompletionQuery

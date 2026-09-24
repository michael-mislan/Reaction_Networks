import proofs.IrrRAFEnumeration.SATRawRectangleBody
import proofs.IrrRAFEnumeration.SATRawDimensions
import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

namespace IrrRAFEnumeration.SATSource
open Complexity SAT Complexity.TM

def rectanglePrepareTM : TM 4 :=
  seqTM (copyIntoTM 0 3) (seqTM (copyIntoTM 1 2)
    (seqTM (clearRegTM 0) (clearRegTM 1)))

def rectanglePrepareBound (N M : Nat) := 2*M*M+9*M+2*N*N+9*N+25

theorem rectanglePrepareTM_correct (N M : Nat) (inp : Tape) (ys : List Bool)
    (hp : Parked inp) :
    rectanglePrepareTM.HoareTime
      (EmitPred inp ![regTape M,regTape N,regTape 0,regTape 0] ys)
      (EmitPred inp (rectangleWork 0 0 (regTape N) (regTape M)) ys)
      (rectanglePrepareBound N M) := by
  let w₀ : Fin 4 → Tape := ![regTape M,regTape N,regTape 0,regTape 0]
  let w₁ : Fin 4 → Tape := ![regTape M,regTape N,regTape 0,regTape M]
  let w₂ : Fin 4 → Tape := ![regTape M,regTape N,regTape N,regTape M]
  let w₃ : Fin 4 → Tape := ![regTape 0,regTape N,regTape N,regTape M]
  have hp₀ : ∀ i, Parked (w₀ i) := by intro i; fin_cases i <;> exact parked_regTape _
  have hp₁ : ∀ i, Parked (w₁ i) := by intro i; fin_cases i <;> exact parked_regTape _
  have hp₂ : ∀ i, Parked (w₂ i) := by intro i; fin_cases i <;> exact parked_regTape _
  have hp₃ : ∀ i, Parked (w₃ i) := by intro i; fin_cases i <;> exact parked_regTape _
  have e₁ : Function.update w₀ 3 (regTape M) = w₁ := by
    funext i; fin_cases i <;> rfl
  have e₂ : Function.update w₁ 2 (regTape N) = w₂ := by
    funext i; fin_cases i <;> rfl
  have e₃ : Function.update w₂ 0 (regTape 0) = w₃ := by
    funext i; fin_cases i <;> rfl
  have e₄ : Function.update w₃ 1 (regTape 0) = rectangleWork 0 0 (regTape N) (regTape M) := by
    funext i; fin_cases i <;> rfl
  have h₁ := copyIntoTM_hoareTime (0 : Fin 4) 3 (by decide) M 0 inp w₀ ys hp
    (fun i _ => hp₀ i) rfl rfl
  have h₂ := copyIntoTM_hoareTime (1 : Fin 4) 2 (by decide) N 0 inp w₁ ys hp
    (fun i _ => hp₁ i) rfl rfl
  have h₃ := clearRegTM_hoareTime (0 : Fin 4) M inp w₂ ys hp (fun i _ => hp₂ i) rfl
  have h₄ := clearRegTM_hoareTime (1 : Fin 4) N inp w₃ ys hp (fun i _ => hp₃ i) rfl
  rw [e₁] at h₁
  rw [e₂] at h₂
  rw [e₃] at h₃
  rw [e₄] at h₄
  have h₃₄ := seqTM_hoareTime _ _ h₃ (emitPred_transition hp hp₃ ys) h₄
  have h₂₃₄ := seqTM_hoareTime _ _ h₂ (emitPred_transition hp hp₂ ys) h₃₄
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hp₁ ys) h₂₃₄
  exact h.mono_bound (le_of_eq (by unfold rectanglePrepareBound; ring))

def rawRectangleSetupTM : TM 4 := seqTM (rawDimensionsTM.liftTM 2) rectanglePrepareTM

theorem rawRectangleSetupTM_correct (φ : CNF) :
    ∃ c t, t ≤ 9*φ.encode.length+28+rectanglePrepareBound (φ.encode.length+2) φ.length ∧
      rawRectangleSetupTM.reachesIn t (rawRectangleSetupTM.initCfg φ.encode) c ∧
      rawRectangleSetupTM.halted c ∧
      c.input = ⟨1,(Tape.init (φ.encode.map Γ.ofBool)).cells⟩ ∧
      c.work = rectangleWork 0 0 (regTape (φ.encode.length+2)) (regTape φ.length) ∧
      OutAcc [] c.output := by
  obtain ⟨d,t,ht,hr,hh,hm,hn,hi,ho⟩ := rawDimensionsTM_encode_correct φ
  have htpos : 0 < t := by
    cases hr with
    | zero => simp [rawDimensionsTM,seqTM,TM.halted,Cfg.isHalted] at hh
    | step => omega
  let a := rawDimensionsTM.liftCfg 2 d
  have ha := liftTM_reachesIn_initCfg_of_pos rawDimensionsTM 2 φ.encode htpos hr
  change (rawDimensionsTM.liftTM 2).reachesIn t
    ((rawDimensionsTM.liftTM 2).initCfg φ.encode) a at ha
  have hw : a.work = ![regTape φ.length,regTape (φ.encode.length+2),regTape 0,regTape 0] := by
    funext i
    fin_cases i
    · exact hm
    · exact hn
    · exact reg_zero_init_bumped.eq_regT
    · exact reg_zero_init_bumped.eq_regT
  have hp : Parked a.input := by rw [show a.input = d.input from rfl,hi]; exact parked_init_input _
  have hwp : ∀ i, Parked (a.work i) := by
    intro i
    rw [hw]
    fin_cases i <;> exact parked_regTape _
  have hop : OutAcc [] a.output := ho
  obtain ⟨c,s,hs,hsr,hsh,hsi,hsw,hso⟩ := rectanglePrepareTM_correct
    (φ.encode.length+2) φ.length a.input [] hp a.input a.work a.output ⟨rfl,hw,hop⟩
  have hwt : (fun i => transitionTape (a.work i)) = a.work :=
    funext (fun i => (hwp i).transitionTape_eq_self)
  have hrun := seqTM_reachesIn_of_reachesIn (rawDimensionsTM.liftTM 2) rectanglePrepareTM
    ha hh (by
      simpa only [hp.transitionInput_eq_self,hwt,hop.parked.transitionTape_eq_self] using hsr)
  refine ⟨phase2Wrap (rawDimensionsTM.liftTM 2) rectanglePrepareTM c,t+1+s,
    by omega,hrun,(phase2Wrap_halted_iff _ _ _).mpr hsh,hsi.trans hi,hsw,hso⟩

end IrrRAFEnumeration.SATSource

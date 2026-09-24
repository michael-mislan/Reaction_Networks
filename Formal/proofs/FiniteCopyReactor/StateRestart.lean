import proofs.FiniteCopyReactor.SwitchedMaterial
import proofs.FiniteCopyReactor.SwitchedStock
import proofs.FiniteCopyReactor.JointCounterBudget

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem switched_event_union (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (A B : Set (BoxCounts V)) (N : BoxCounts V) :
    switchedState V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator (A ∪ B)) N ≤
      switchedState V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator A) N+
      switchedState V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator B) N := by
  have h := joint_cycle_event_union V r d hV hr hr' hd hd'
    {X | X.1 ∈ A} {X | X.1 ∈ B} N (initialCounters 0 0)
  change jointCycle V r d hV hr hr' hd hd' (fun X => FiniteKernel.eventIndicator (A ∪ B) X.1) N (initialCounters 0 0) ≤
    jointCycle V r d hV hr hr' hd hd' (fun X => FiniteKernel.eventIndicator A X.1) N (initialCounters 0 0)+
    jointCycle V r d hV hr hr' hd hd' (fun X => FiniteKernel.eventIndicator B X.1) N (initialCounters 0 0) at h
  simpa only [joint_state_marginal] using h

def StateRestartFailure (V : ℕ) : Set (BoxCounts V) :=
  ({X | ¬resourceGood (boxCounts X) V} ∪ {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}) ∪
    ((ActiveMaterialTail V true 1 ∪ ActiveMaterialTail V true (-1)) ∪
     (ActiveMaterialTail V false 1 ∪ ActiveMaterialTail V false (-1)))

def stateRestartError (V : ℝ) : ℝ :=
  materialExitError V+collectionResidenceError V+4*(Real.exp (-V/320000)+Real.exp (-V))

theorem state_restart_failure_bound (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧ unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    switchedState V r d hV (by linarith) hr' hd hd' (FiniteKernel.eventIndicator (StateRestartFailure V)) N ≤ stateRestartError V := by
  let C := fun A => switchedState V r d hV (by linarith) hr' hd hd' (FiniteKernel.eventIndicator A) N
  have hU (A B) : C (A ∪ B) ≤ C A+C B := switched_event_union V r d hV (by linarith) hr' hd hd' A B N
  have hm : C {X | ¬resourceGood (boxCounts X) V} ≤ materialExitError V := switched_material_exit V r d hV hr hr' hd hd' N hprep
  have hs : C {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20} ≤ collectionResidenceError V := switched_stock_exit V r d hV hr hr' hd hd' N hstock hprep
  have ht (side : Bool) (sign : ℝ) (hsgn : |sign|=1) : C (ActiveMaterialTail V side sign) ≤
      Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) :=
    switched_material_tail V side sign r d hV hsgn hr hr' hd hd' N
      (by rw [abs_le]; constructor <;> linarith [(hprep side).1,(hprep side).2])
  have hB (side : Bool) := hU (ActiveMaterialTail V side 1) (ActiveMaterialTail V side (-1))
  have hM := hU {X | ¬resourceGood (boxCounts X) V} {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20}
  have hT := hU (ActiveMaterialTail V true 1 ∪ ActiveMaterialTail V true (-1))
    (ActiveMaterialTail V false 1 ∪ ActiveMaterialTail V false (-1))
  have hA := hU ({X | ¬resourceGood (boxCounts X) V} ∪ {X | weightedCount (boxCounts X) ≤ (V:ℝ)/20})
    ((ActiveMaterialTail V true 1 ∪ ActiveMaterialTail V true (-1)) ∪ (ActiveMaterialTail V false 1 ∪ ActiveMaterialTail V false (-1)))
  change C _ ≤ _
  unfold StateRestartFailure stateRestartError
  linarith [hB true,hB false,ht true 1 (by norm_num),ht true (-1) (by norm_num),ht false 1 (by norm_num),ht false (-1) (by norm_num)]

theorem outside_state_restart_failure (V : ℕ) (X : BoxCounts V) (h : X ∉ StateRestartFailure V) :
    residenceActive V X ∧ Restart V (boxCounts X) := by
  have hm : resourceGood (boxCounts X) V := by
    by_contra hn
    exact h (Or.inl (Or.inl hn))
  have hs : (V:ℝ)/20 < weightedCount (boxCounts X) := by
    by_contra hn
    exact h (Or.inl (Or.inr (le_of_not_gt hn)))
  have ha : residenceActive V X := ⟨hm,hs⟩
  have ht (side : Bool) : (159/160)*(V:ℝ) ≤ unitObs side (boxCounts X) ∧ unitObs side (boxCounts X) ≤ (161/160)*(V:ℝ) := by
    have hp : ¬(V:ℝ)/160 ≤ unitObs side (boxCounts X)-(V:ℝ) := by
      intro hp
      cases side with
      | false => exact h (Or.inr (Or.inr (Or.inl ⟨ha,by simpa using hp⟩)))
      | true => exact h (Or.inr (Or.inl (Or.inl ⟨ha,by simpa using hp⟩)))
    have hn : ¬(V:ℝ)/160 ≤ -(unitObs side (boxCounts X)-(V:ℝ)) := by
      intro hn
      cases side with
      | false => exact h (Or.inr (Or.inr (Or.inr ⟨ha,by simpa using hn⟩)))
      | true => exact h (Or.inr (Or.inl (Or.inr ⟨ha,by simpa using hn⟩)))
    constructor <;> linarith
  have hy : 2*V ≤ stockInteger (boxCounts X) := by
    have hh := stock_integer_real (boxCounts X)
    have hh' : (2:ℝ)*V ≤ stockInteger (boxCounts X) := by linarith
    exact_mod_cast hh'
  refine ⟨ha,?_⟩
  unfold Restart
  have hu := ht true
  have hw := ht false
  change _ ≤ uCount (boxCounts X) ∧ uCount (boxCounts X) ≤ _ at hu
  change _ ≤ wCount (boxCounts X) ∧ wCount (boxCounts X) ≤ _ at hw
  refine ⟨?_,?_,?_,?_,hy⟩ <;> linarith [hu.1,hu.2,hw.1,hw.2]

end
end FiniteCopyReactor

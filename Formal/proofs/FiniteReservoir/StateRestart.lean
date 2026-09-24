import proofs.FiniteReservoir.SwitchedMaterial
import proofs.FiniteReservoir.SwitchedStock
import proofs.FiniteReservoir.JointCounterBudget

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

theorem switched_event_union (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (A B : Set (BoxState V M)) (N : BoxState V M) :
    switchedState V M p hV (FiniteKernel.eventIndicator (A ∪ B)) N ≤
      switchedState V M p hV (FiniteKernel.eventIndicator A) N+
      switchedState V M p hV (FiniteKernel.eventIndicator B) N := by
  have h := joint_cycle_event_union V M p hV
    {X | X.1 ∈ A} {X | X.1 ∈ B} N (initialCounters 0 0)
  change jointCycle V M p hV (fun X => FiniteKernel.eventIndicator (A ∪ B) X.1) N (initialCounters 0 0) ≤
    jointCycle V M p hV (fun X => FiniteKernel.eventIndicator A X.1) N (initialCounters 0 0)+
    jointCycle V M p hV (fun X => FiniteKernel.eventIndicator B X.1) N (initialCounters 0 0) at h
  simpa only [joint_state_marginal] using h

def StateRestartFailure (V M : ℕ) : Set (BoxState V M) :=
  ({X | ¬resourceGood (boxCounts X.1) V} ∪ {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}) ∪
    ((ActiveMaterialTail V M true 1 ∪ ActiveMaterialTail V M true (-1)) ∪
     (ActiveMaterialTail V M false 1 ∪ ActiveMaterialTail V M false (-1)))

def stateRestartError (V : ℝ) : ℝ :=
  materialExitError V+collectionResidenceError V+4*(Real.exp (-V/320000)+Real.exp (-V))

theorem state_restart_failure_bound (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧ unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ)) :
    switchedState V M p hV (FiniteKernel.eventIndicator (StateRestartFailure V M)) N ≤ stateRestartError V := by
  let C := fun A => switchedState V M p hV (FiniteKernel.eventIndicator A) N
  have hU (A B) : C (A ∪ B) ≤ C A+C B := switched_event_union V M p hV A B N
  have hm : C {X | ¬resourceGood (boxCounts X.1) V} ≤ materialExitError V := switched_material_exit V M p hV N hprep
  have hs : C {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20} ≤ collectionResidenceError V := switched_stock_exit V M p hV N hstock hprep
  have ht (side : Bool) (sign : ℝ) (hsgn : |sign|=1) : C (ActiveMaterialTail V M side sign) ≤
      Real.exp (-(V:ℝ)/320000)+Real.exp (-(V:ℝ)) :=
    switched_material_tail V M side sign p hV hsgn N
      (by rw [abs_le]; constructor <;> linarith [(hprep side).1,(hprep side).2])
  have hB (side : Bool) := hU (ActiveMaterialTail V M side 1) (ActiveMaterialTail V M side (-1))
  have hM := hU {X | ¬resourceGood (boxCounts X.1) V} {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20}
  have hT := hU (ActiveMaterialTail V M true 1 ∪ ActiveMaterialTail V M true (-1))
    (ActiveMaterialTail V M false 1 ∪ ActiveMaterialTail V M false (-1))
  have hA := hU ({X | ¬resourceGood (boxCounts X.1) V} ∪ {X | weightedCount (boxCounts X.1) ≤ (V:ℝ)/20})
    ((ActiveMaterialTail V M true 1 ∪ ActiveMaterialTail V M true (-1)) ∪ (ActiveMaterialTail V M false 1 ∪ ActiveMaterialTail V M false (-1)))
  change C _ ≤ _
  unfold StateRestartFailure stateRestartError
  linarith [hB true,hB false,ht true 1 (by norm_num),ht true (-1) (by norm_num),ht false 1 (by norm_num),ht false (-1) (by norm_num)]

theorem outside_state_restart_failure (V M : ℕ) (X : BoxState V M) (h : X ∉ StateRestartFailure V M) :
    residenceActive V X.1 ∧ Restart V (boxCounts X.1) := by
  have hm : resourceGood (boxCounts X.1) V := by
    by_contra hn
    exact h (Or.inl (Or.inl hn))
  have hs : (V:ℝ)/20 < weightedCount (boxCounts X.1) := by
    by_contra hn
    exact h (Or.inl (Or.inr (le_of_not_gt hn)))
  have ha : residenceActive V X.1 := ⟨hm,hs⟩
  have ht (side : Bool) : (159/160)*(V:ℝ) ≤ unitObs side (boxCounts X.1) ∧ unitObs side (boxCounts X.1) ≤ (161/160)*(V:ℝ) := by
    have hp : ¬(V:ℝ)/160 ≤ unitObs side (boxCounts X.1)-(V:ℝ) := by
      intro hp
      cases side with
      | false => exact h (Or.inr (Or.inr (Or.inl ⟨ha,by simpa using hp⟩)))
      | true => exact h (Or.inr (Or.inl (Or.inl ⟨ha,by simpa using hp⟩)))
    have hn : ¬(V:ℝ)/160 ≤ -(unitObs side (boxCounts X.1)-(V:ℝ)) := by
      intro hn
      cases side with
      | false => exact h (Or.inr (Or.inr (Or.inr ⟨ha,by simpa using hn⟩)))
      | true => exact h (Or.inr (Or.inl (Or.inr ⟨ha,by simpa using hn⟩)))
    constructor <;> linarith
  have hy : 2*V ≤ stockInteger (boxCounts X.1) := by
    have hh := stock_integer_real (boxCounts X.1)
    have hh' : (2:ℝ)*V ≤ stockInteger (boxCounts X.1) := by linarith
    exact_mod_cast hh'
  refine ⟨ha,?_⟩
  unfold Restart
  have hu := ht true
  have hw := ht false
  change _ ≤ uCount (boxCounts X.1) ∧ uCount (boxCounts X.1) ≤ _ at hu
  change _ ≤ wCount (boxCounts X.1) ∧ wCount (boxCounts X.1) ≤ _ at hw
  refine ⟨?_,?_,?_,?_,hy⟩ <;> linarith [hu.1,hu.2,hw.1,hw.2]

end
end FiniteReservoir

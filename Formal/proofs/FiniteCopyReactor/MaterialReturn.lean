import proofs.FiniteCopyReactor.TerminalMaterialProbability
import proofs.FiniteCopyReactor.MaterialPulse
import proofs.FiniteCopy.KernelExpectations

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem event_nonneg {α : Type*} (E : Set α) (x : α) :
    0 ≤ FiniteKernel.eventIndicator E x := by
  unfold FiniteKernel.eventIndicator
  split_ifs <;> norm_num

theorem event_union_bound {α : Type*} [Fintype α] (P : FiniteKernel α)
    (t : ℝ≥0) (A B : Set α) (x : α) :
    P.poissonized t (FiniteKernel.eventIndicator (A ∪ B)) x ≤
      P.poissonized t (FiniteKernel.eventIndicator A) x +
      P.poissonized t (FiniteKernel.eventIndicator B) x := by
  have h := P.poissonized_mono t _ _ (event_nonneg (A ∪ B))
    (fun y => add_nonneg (event_nonneg A y) (event_nonneg B y))
    (fun y => show FiniteKernel.eventIndicator (A ∪ B) y ≤
      FiniteKernel.eventIndicator A y + FiniteKernel.eventIndicator B y by
      simp only [FiniteKernel.eventIndicator,Set.mem_union]
      split_ifs <;> simp_all) x
  rwa [P.poissonized_add t _ _ (event_nonneg A) (event_nonneg B)] at h

def MaterialReturnFailure (V : ℕ) : Set (BoxCounts V) :=
  {X | ¬resourceGood (boxCounts X) V} ∪
    ((TerminalMaterialTail V true 1 ∪ TerminalMaterialTail V true (-1)) ∪
     (TerminalMaterialTail V false 1 ∪ TerminalMaterialTail V false (-1)))

theorem outside_material_return_failure (V : ℕ) (X : BoxCounts V)
    (h : X ∉ MaterialReturnFailure V) (side : Bool) :
    (159/160)*(V:ℝ) ≤ unitObs side (boxCounts X) ∧
      unitObs side (boxCounts X) ≤ (161/160)*(V:ℝ) := by
  have hg : resourceGood (boxCounts X) V := by
    by_contra hc
    exact h (Or.inl hc)
  have hp : ¬(V:ℝ)/160 ≤ unitObs side (boxCounts X)-(V:ℝ) := by
    intro hp
    cases side with
    | false => exact h (Or.inr (Or.inr (Or.inl ⟨hg,by simpa using hp⟩)))
    | true => exact h (Or.inr (Or.inl (Or.inl ⟨hg,by simpa using hp⟩)))
  have hm : ¬(V:ℝ)/160 ≤ -(unitObs side (boxCounts X)-(V:ℝ)) := by
    intro hm
    cases side with
    | false => exact h (Or.inr (Or.inr (Or.inr ⟨hg,by simpa using hm⟩)))
    | true => exact h (Or.inr (Or.inl (Or.inr ⟨hg,by simpa using hm⟩)))
  constructor <;> linarith

def materialReturnError (V : ℝ) : ℝ :=
  materialExitError V + 4*(Real.exp (-V/320000)+Real.exp (-V))

theorem prepared_material_return (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (N : BoxCounts V)
    (h : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N) ∧
      unitObs side (boxCounts N) ≤ (51/50)*(V:ℝ)) :
    (materialKernel V r d hV hr hr' hd hd').poissonized ((12000:ℝ≥0)*V)
      (FiniteKernel.eventIndicator (MaterialReturnFailure V)) N ≤ materialReturnError V := by
  let P := materialKernel V r d hV hr hr' hd hd'
  let t : ℝ≥0 := 12000*V
  have ht (side : Bool) (s : ℝ) (hs : |s|=1) :=
    terminal_material_signed_probability V side s r d hV hs hr hr' hd hd' N
      (show |unitObs side (boxCounts N)-(V:ℝ)| ≤ (V:ℝ)/25 by
        rw [abs_le]; constructor <;> linarith [(h side).1,(h side).2])
  have hb (side : Bool) := (event_union_bound P t
    (TerminalMaterialTail V side 1) (TerminalMaterialTail V side (-1)) N).trans
    (add_le_add (ht side 1 (by norm_num)) (ht side (-1) (by norm_num)))
  have hu := event_union_bound P t
    (TerminalMaterialTail V true 1 ∪ TerminalMaterialTail V true (-1))
    (TerminalMaterialTail V false 1 ∪ TerminalMaterialTail V false (-1)) N
  have he := prepared_material_exit V r d hV hr hr' hd hd' N h
  have htime : (3000:ℝ≥0)*V*4 = (12000:ℝ≥0)*V := by ring
  rw [htime] at he
  have hall := event_union_bound P t {X | ¬resourceGood (boxCounts X) V}
    ((TerminalMaterialTail V true 1 ∪ TerminalMaterialTail V true (-1)) ∪
     (TerminalMaterialTail V false 1 ∪ TerminalMaterialTail V false (-1))) N
  change _ ≤ materialReturnError V
  unfold MaterialReturnFailure materialReturnError
  exact hall.trans (by linarith [hu,hb true,hb false])

end
end FiniteCopyReactor

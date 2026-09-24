import proofs.FiniteReservoir.SupplySource
import proofs.FiniteReservoir.CollectionResidence
import proofs.FiniteCopyReactor.MarkedUpper

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators NNReal

def supplyModel (stopStock : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  if stopStock then residenceModel V M p hV else materialModel V M p hV

theorem supply_total_bound (b : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M) :
    (supplyModel b V M p hV).total N ≤ 3000*(V:ℝ) := by
  cases b
  · exact material_total V M p hV N
  · exact residence_total V M p hV N

def supplyKernel (b : Bool) (k : SupplyKind) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  (supplyModel b V M p hV).withMarks (supplyMark k) (3000*(V:ℝ))
    (by positivity) (supply_total_bound b V M p hV)

theorem supply_model_intensity (b : Bool) (k : SupplyKind) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (N : BoxState V M) :
    (∑ j,(supplyModel b V M p hV).rate N j*supplyMark k j) ≤ supplyRateCap k*(V:ℝ) := by
  have hlocal (active : Counts → Prop) (ha : ∀ X, active X → resourceGood X V) :
      (∑ j,(model V M p hV active).rate N j*supplyMark k j) ≤ supplyRateCap k*(V:ℝ) := by
    by_cases hc : active (boxCounts N.1)
    · simp only [model,if_pos hc,rate_binding,boxState]
      exact supply_intensity_bound k (boxCounts N.1) V p.release _ _ hV (parameters_box p N.2) (ha _ hc)
    · simp only [model,if_neg hc,zero_mul,Finset.sum_const_zero]
      exact mul_nonneg (supply_rate_cap_nonneg k) hV.le
  cases b
  · exact hlocal (fun X => resourceGood X V) (fun _ h => h)
  · exact hlocal (fun X => resourceGood X V ∧ (V:ℝ)/20 < weightedCount X) (fun _ h => h.1)


theorem supply_exponential_step (b : Bool) (k : SupplyKind) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     (s : ℝ) (hs : 0 ≤ s)
    (N : BoxState V M) (z : ℝ) :
    (supplyKernel b k V M p hV).step (fun _ w => Real.exp (s*w)) N z ≤
      (1+(supplyRateCap k/3000)*(Real.exp s-1))*Real.exp (s*z) := by
  let P := supplyKernel b k V M p hV
  have hm (j) : P.mark j=0 ∨ P.mark j=1 := by
    cases j with
    | none => exact Or.inl rfl
    | some j => exact supply_mark_binary k j
  apply bernoulli_mark_step P hm (supplyRateCap k/3000) s hs
  intro X
  simp only [P,supplyKernel,FiniteJumpModel.withMarks,Fintype.sum_option,mul_zero,zero_add,
    div_mul_eq_mul_div,← Finset.sum_div]
  apply (div_le_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
  have h := supply_model_intensity b k V M p hV X
  convert h using 1
  ring

end
end FiniteReservoir

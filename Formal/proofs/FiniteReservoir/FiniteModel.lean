import proofs.FiniteReservoir.RateBounds
import proofs.FiniteReservoir.StockExponential
import proofs.FiniteReservoir.PhaseBounds

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped BigOperators

/-- A fixed finite bath class; the second coordinate is determined by conservation. -/
abbrev FuelState (M : ℕ) := Fin (M+1)
def bathOf {M : ℕ} (f : FuelState M) : Bath := ⟨f.val,M-f.val⟩
theorem bathOf_total {M : ℕ} (f : FuelState M) : (bathOf f).total=M := by
  have := f.isLt
  simp only [bathOf,Bath.total]
  omega

structure Parameters (M : ℕ) where
  capacity : ℝ
  capacity_pos : 0 < capacity
  release : ℝ
  release_lower : 19 ≤ release
  release_upper : release ≤ 21
  cleavage : ℝ
  cleavage_nonneg : 0 ≤ cleavage
  inventory_bound : cleavage*M ≤ capacity/25

theorem parameters_box {M : ℕ} (p : Parameters M) (f : FuelState M) :
    RateBox (alpha (bathOf f) p.cleavage p.capacity)
      (beta (bathOf f) p.cleavage p.capacity) := by
  apply rate_box _ _ _ p.capacity_pos p.cleavage_nonneg
  · have hf : ((bathOf f).fuel:ℝ) ≤ M := by
      exact_mod_cast (show (bathOf f).fuel ≤ M by have := bathOf_total f; unfold Bath.total at this; omega)
    exact (mul_le_mul_of_nonneg_left hf p.cleavage_nonneg).trans p.inventory_bound
  · have hp : ((bathOf f).waste:ℝ) ≤ M := by
      exact_mod_cast (show (bathOf f).waste ≤ M by have := bathOf_total f; unfold Bath.total at this; omega)
    exact (mul_le_mul_of_nonneg_left hp p.cleavage_nonneg).trans p.inventory_bound

def fuelNext {M : ℕ} (f : FuelState M) : CompetitionChannel → FuelState M
  | .inl _ => f
  | .inr j => if j=0 then ⟨f.val-1,by omega⟩
      else ⟨min (f.val+1) M,by omega⟩

abbrev BoxState (V M : ℕ) := BoxCounts V × FuelState M
def boxState {V M : ℕ} (X : BoxState V M) : State := (boxCounts X.1,bathOf X.2)
def boxNext (V M : ℕ) (X : BoxState V M) (j : CompetitionChannel) : BoxState V M :=
  (RandomViability.Binding.boxNext V X.1 (competitionBase j),fuelNext X.2 j)

def model (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (active : Counts → Prop) : FiniteJumpModel (BoxState V M) CompetitionChannel where
  next := boxNext V M
  rate X j := if active (boxCounts X.1) then
    rate (boxState X) V p.release p.cleavage p.capacity j else 0
  nonneg X j := by
    split_ifs
    · exact bath_rate_nonneg _ _ _ _ _ hV (by linarith [p.release_lower])
        p.cleavage_nonneg p.capacity_pos j
    · rfl

theorem model_inside (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (active : Counts → Prop) (X : BoxState V M) (h : active (boxCounts X.1))
    (hc : resourceGood (boxCounts X.1) V) (f : Counts → ℝ) :
    (model V M p hV active).generator (fun Y => f (boxCounts Y.1)) X =
      generator (boxCounts X.1) V p.release
        (alpha (bathOf X.2) p.cleavage p.capacity) (beta (bathOf X.2) p.cleavage p.capacity) f := by
  simp only [FiniteJumpModel.generator,model,if_pos h,generator]
  apply Finset.sum_congr rfl
  intro j _
  rw [rate_binding]
  change _*(f (boxCounts (RandomViability.Binding.boxNext V X.1 (competitionBase j)))-_)=_
  rw [boxNext_exact V X.1 (competitionBase j) hc]
  rfl

theorem model_outside (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (active : Counts → Prop) (X : BoxState V M) (h : ¬active (boxCounts X.1))
    (f : BoxState V M → ℝ) : (model V M p hV active).generator f X=0 := by
  simp [FiniteJumpModel.generator,model,h]

theorem model_total (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (active : Counts → Prop) (ha : ∀ N,active N → resourceGood N V) (X : BoxState V M) :
    (model V M p hV active).total X ≤ 3000*(V:ℝ) := by
  by_cases h : active (boxCounts X.1)
  · simp only [FiniteJumpModel.total,model,if_pos h,rate_binding]
    exact total_rate_bound _ V p.release _ _ hV (by linarith [p.release_lower])
      p.release_upper (parameters_box p X.2) (ha _ h)
  · simp only [FiniteJumpModel.total,model,if_neg h,Finset.sum_const_zero]
    positivity

theorem corridor_stock_exponential (N : Counts) (V : ℕ) (r alpha beta s : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hbox : RateBox alpha beta)
    (hcor : resourceGood N V) (hY : weightedCount N ≤ (3/50)*(V:ℝ))
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) :
    generator N V r alpha beta (fun X => Real.exp (-s*weightedCount X)) ≤
      Real.exp (-s*weightedCount N)*(-(5/8)*s*weightedCount N) := by
  have ha : A (FiniteCopyReactor.concentration N V)=uCount N/(V:ℝ) := by
    rw [uCount_expansion]; dsimp [A,FiniteCopyReactor.concentration]; ring
  have hb : B (FiniteCopyReactor.concentration N V)=wCount N/(V:ℝ) := by
    rw [wCount_expansion]; dsimp [B,FiniteCopyReactor.concentration]; ring
  have hc (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V hcor i)
  apply stock_exponential_drift N V r alpha beta s hV hr hr' hbox
  · rw [ha]; exact (le_div_iff₀ hV).mpr hcor.1
  · rw [hb]; exact (le_div_iff₀ hV).mpr hcor.2.2.1
  · rw [FiniteCopyReactor.normalized_stock]; exact (div_le_iff₀ hV).mpr hY
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hs
  · exact hs'

end
end FiniteReservoir

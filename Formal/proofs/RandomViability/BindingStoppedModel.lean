import proofs.RandomViability.BindingMoietyDrift
import proofs.RandomViability.BindingRateBound
import proofs.FiniteCopy.FiniteJump

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators
open FiniteCopy Classical

set_option maxHeartbeats 20000

abbrev BoxCounts (V : ℕ) := Fin 6 → Fin (3*V+3)
def boxCounts {V : ℕ} (N : BoxCounts V) : Counts := fun i => (N i).val

/-- The declared operating resource corridor, expressed in preserved units. -/
def resourceGood (N : Counts) (V : ℕ) : Prop :=
  (9/10)*(V:ℝ) ≤ uCount N ∧ uCount N ≤ (11/10)*(V:ℝ) ∧
  (9/10)*(V:ℝ) ≤ wCount N ∧ wCount N ≤ (11/10)*(V:ℝ)

theorem count_le_units (N : Counts) (i : Fin 6) :
    (N i:ℝ) ≤ max (uCount N) (wCount N) := by
  have hn (j : Fin 6) : 0 ≤ (N j:ℝ) := Nat.cast_nonneg _
  fin_cases i
  · apply le_trans ?_ (le_max_left (uCount N) (wCount N))
    rw [uCount_expansion]
    change (N 0:ℝ) ≤ _
    linarith [hn 2,hn 3,hn 4,hn 5]
  · apply le_trans ?_ (le_max_right (uCount N) (wCount N))
    rw [wCount_expansion]
    change (N 1:ℝ) ≤ _
    linarith [hn 2,hn 3,hn 4,hn 5]
  · apply le_trans ?_ (le_max_left (uCount N) (wCount N))
    rw [uCount_expansion]
    change (N 2:ℝ) ≤ _
    linarith [hn 0,hn 3,hn 4,hn 5]
  · apply le_trans ?_ (le_max_left (uCount N) (wCount N))
    rw [uCount_expansion]
    change (N 3:ℝ) ≤ _
    linarith [hn 0,hn 2,hn 3,hn 4,hn 5]
  · apply le_trans ?_ (le_max_left (uCount N) (wCount N))
    rw [uCount_expansion]
    change (N 4:ℝ) ≤ _
    linarith [hn 0,hn 2,hn 3,hn 4,hn 5]
  · apply le_trans ?_ (le_max_left (uCount N) (wCount N))
    rw [uCount_expansion]
    change (N 5:ℝ) ≤ _
    linarith [hn 0,hn 2,hn 3,hn 4,hn 5]

theorem resource_count_cap (N : Counts) (V : ℕ) (h : resourceGood N V) (i : Fin 6) :
    (N i:ℝ) ≤ (11/10)*(V:ℝ) :=
  (count_le_units N i).trans (max_le h.2.1 h.2.2.2)

theorem products_cap (j : Fin 18) (i : Fin 6) : products j i ≤ 2 := by
  have h : ∀ j : Fin 18, ∀ i : Fin 6, products j i ≤ 2 := by decide
  exact h j i

/-- The outer finite box never clips a transition from the operating region.
Thus sending resource exits to absorbing failure does not reflect paths. -/
theorem resource_next_in_box (N : Counts) (V : ℕ) (h : resourceGood N V)
    (j : Fin 18) (i : Fin 6) : countNext N j i < 3*V+3 := by
  have hn : countNext N j i ≤ N i+2 :=
    Nat.add_le_add (Nat.sub_le _ _) (products_cap j i)
  have hr : (countNext N j i:ℝ) ≤ (N i:ℝ)+2 := by exact_mod_cast hn
  have hc := resource_count_cap N V h i
  have hh : (countNext N j i:ℝ) < 3*(V:ℝ)+3 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) V]
  exact_mod_cast hh

def boxNext (V : ℕ) (N : BoxCounts V) (j : Fin 18) : BoxCounts V :=
  if h : ∀ i,countNext (boxCounts N) j i < 3*V+3 then
    fun i => ⟨countNext (boxCounts N) j i,h i⟩ else N

theorem boxNext_exact (V : ℕ) (N : BoxCounts V) (j : Fin 18)
    (h : resourceGood (boxCounts N) V) :
    boxCounts (boxNext V N j) = countNext (boxCounts N) j := by
  have hb := resource_next_in_box (boxCounts N) V h j
  unfold boxNext
  rw [dif_pos hb]
  rfl

def stoppedRate (V : ℕ) (eps k r : ℝ) (N : BoxCounts V) (j : Fin 18) : ℝ :=
  if resourceGood (boxCounts N) V then countRate (boxCounts N) V eps k r j else 0

def stoppedModel (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    FiniteJumpModel (BoxCounts V) (Fin 18) where
  next := boxNext V
  rate := stoppedRate V eps k r
  nonneg N j := by
    dsimp [stoppedRate]
    split_ifs
    · exact countRate_nonneg (boxCounts N) V eps k r hV heps hk hr j
    · rfl

theorem stopped_total_bound (V : ℕ) (eps k r : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 0 ≤ r) (hr22 : r ≤ 22) (N : BoxCounts V) :
    (stoppedModel V eps k r hV heps hk hr).total N ≤ 3000*(V:ℝ) := by
  by_cases h : resourceGood (boxCounts N) V
  · simp only [FiniteJumpModel.total,stoppedModel,stoppedRate,if_pos h]
    apply total_rate_bound (boxCounts N) V eps k r hV heps heps1 hk hk1 hr hr22
    intro i
    have hi := resource_count_cap (boxCounts N) V h i
    linarith
  · simp only [FiniteJumpModel.total,stoppedModel,stoppedRate,if_neg h,Finset.sum_const_zero]
    positivity

end
end RandomViability.Binding


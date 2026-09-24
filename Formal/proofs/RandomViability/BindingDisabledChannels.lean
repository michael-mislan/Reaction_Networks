import proofs.RandomViability.BindingOutputModel

namespace RandomViability.Binding
noncomputable section
open Classical
open scoped BigOperators

/-- Remove both catalytic ligation directions, retaining basal and binding reactions. -/
def disabledRate (N : Counts) (V eps k r : ℝ) (j : Fin 18) : ℝ :=
  if j=6 ∨ j=7 then 0 else countRate N V eps k r j

def disabledGenerator (N : Counts) (V eps k r : ℝ) (f : Counts → ℝ) : ℝ :=
  ∑ j,disabledRate N V eps k r j*(f (countNext N j)-f N)

theorem disabledRate_nonneg (N : Counts) (V eps k r : ℝ) (hV : 0<V)
    (heps : 0≤eps) (hk : 0≤k) (hr : 0≤r) (j : Fin 18) : 0≤disabledRate N V eps k r j := by
  unfold disabledRate
  split_ifs
  · rfl
  · exact countRate_nonneg N V eps k r hV heps hk hr j

theorem disabledRate_le (N : Counts) (V eps k r : ℝ) (hV : 0<V)
    (heps : 0≤eps) (hk : 0≤k) (hr : 0≤r) (j : Fin 18) : disabledRate N V eps k r j≤countRate N V eps k r j := by
  unfold disabledRate
  split_ifs
  · exact countRate_nonneg N V eps k r hV heps hk hr j
  · rfl

theorem disabled_covalent_balance (N : Counts) (V eps k r : ℝ) :
    (∑ j,disabledRate N V eps k r j*(countProduct (countNext N j)-countProduct N+exportMark j)) =
      4*eps*(N 0)*(N 1)/V-4*eps*k*(N 2) := by
  have hid (j : Fin 18) : disabledRate N V eps k r j*
      (countProduct (countNext N j)-countProduct N+exportMark j) =
      disabledRate N V eps k r j*(basalMark j+catalyticMark j) := by
    unfold disabledRate
    split_ifs
    · simp
    · have h := rated_product_change N V eps k r j
      nlinarith only [h]
  simp only [hid]
  norm_num [disabledRate,countRate,basalMark,catalyticMark,Fin.sum_univ_succ,Fin.ext_iff]
  ring

theorem unit_mark_catalytic_zero (side : Bool) (j : Fin 18) (hj : j=6 ∨ j=7) : unitMark side j=0 := by
  rcases hj with rfl | rfl <;> cases side <;> rfl

theorem disabled_resource_generator (N : Counts) (V eps k r : ℝ) :
    disabledGenerator N V eps k r (resourcePotential V) = literalGenerator N V eps k r (resourcePotential V) := by
  unfold disabledGenerator literalGenerator
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j=6 ∨ j=7
  · by_cases hz : countRate N V eps k r j=0
    · simp [disabledRate,hj,hz]
    · have h₁ := unit_actual_jump true N j (rate_support N V eps k r j hz)
      have h₂ := unit_actual_jump false N j (rate_support N V eps k r j hz)
      rw [unit_mark_catalytic_zero true j hj] at h₁
      rw [unit_mark_catalytic_zero false j hj] at h₂
      have hu : unitObs true (countNext N j)=unitObs true N := by linarith
      have hw : unitObs false (countNext N j)=unitObs false N := by linarith
      have he : resourcePotential V (countNext N j)=resourcePotential V N := by
        unfold resourcePotential upperUnitPotential lowerUnitPotential
        rw [hu,hw]
      simp [disabledRate,hj,he]
  · simp [disabledRate,hj]

theorem countProduct_nonneg (N : Counts) : 0≤countProduct N := by
  norm_num [countProduct,productSpecies,Fin.sum_univ_succ]
  positivity

theorem disabled_basal_bound (N : Counts) (V eps k r : ℝ) (hV : 0<V)
    (heps : 0≤eps) (hk : 0≤k)
    (hu : (N 0:ℝ)≤(11/10)*V) (hw : (N 1:ℝ)≤(11/10)*V) :
    (∑ j,disabledRate N V eps k r j*(countProduct (countNext N j)-countProduct N+exportMark j)) ≤
      (121/25)*eps*V := by
  rw [disabled_covalent_balance]
  have hp := mul_le_mul hu hw (Nat.cast_nonneg (α := ℝ) (N 1)) (by positivity : (0:ℝ)≤(11/10)*V)
  have hd := div_le_div_of_nonneg_right hp hV.le
  have hm := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤4*eps by positivity)
  have he : ((11/10)*V*((11/10)*V))/V = (121/100)*V := by field_simp; ring
  rw [he] at hm
  have hn : 0≤4*eps*k*(N 2:ℝ) := by positivity
  rw [show 4*eps*(N 0:ℝ)*(N 1)/V=4*eps*((N 0:ℝ)*(N 1)/V) by ring]
  nlinarith only [hm,hn]

end
end RandomViability.Binding

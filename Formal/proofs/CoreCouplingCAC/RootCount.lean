import proofs.CoreCouplingCAC.CreationRegime
import Mathlib.Algebra.Polynomial.RuleOfSigns

open Polynomial
namespace CoreCouplingCAC
set_option maxHeartbeats 20000

noncomputable def countCoeff (e : ℝ) : Fin 7 → ℝ :=
  fun i => if i.val = 0 then -533386668-5333866680*e else
    if i.val = 1 then 2490844536-53338666800*e else
    if i.val = 2 then 17625654572+5321310601944*e else
    if i.val = 3 then -56063923056+9698165540064*e else
    if i.val = 4 then -58946493844+19289023400056*e else
    if i.val = 5 then 105146857080+13527216754000*e else 93428004500+10222548740200*e
noncomputable def countPoly (e : ℝ) : ℝ[X] := ∑ i : Fin 7, monomial i.val (countCoeff e i)

theorem count_coeff_signs (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    countCoeff e 0 < 0 ∧ 0 < countCoeff e 1 ∧ 0 < countCoeff e 2 ∧
    countCoeff e 3 < 0 ∧ countCoeff e 4 < 0 ∧ 0 < countCoeff e 5 ∧ 0 < countCoeff e 6 := by
  norm_num [countCoeff]
  repeat' constructor
  all_goals linarith

theorem count_degree (e : ℝ) (h : 0 < countCoeff e 6) : (countPoly e).degree = 6 := by
  apply degree_eq_of_le_of_coeff_ne_zero
  · apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro i _
    exact (degree_monomial_le _ _).trans (by exact_mod_cast (show i.val ≤ 6 by omega))
  · simpa [countPoly,Fin.sum_univ_succ,Polynomial.coeff_monomial] using ne_of_gt h

theorem count_variations (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    (countPoly e).signVariations = 3 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := count_coeff_signs e hl hr
  rw [signVariations,coeffList,count_degree e h6]
  norm_num [countPoly,Fin.sum_univ_succ,Polynomial.coeff_monomial,List.range_succ,Function.comp_apply]
  dsimp [countCoeff] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp only [sign_neg h0,sign_pos h1,sign_pos h2,
    sign_neg h3,sign_neg h4,sign_pos h5,sign_pos h6]
  decide

theorem positive_count_bound (e : ℝ) (hl : (1/200000:ℝ) ≤ e) (hr : e ≤ (1/50000:ℝ)) :
    (countPoly e).roots.countP (0 < ·) ≤ 3 := by
  rw [← count_variations e hl hr]
  exact roots_countP_pos_le_signVariations _

end CoreCouplingCAC

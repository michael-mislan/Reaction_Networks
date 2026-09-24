import proofs.RandomViability.BindingCompetitionSource
import proofs.RandomViability.BindingRateBound

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def covalentCount (N : Counts) : ℝ := ∑ i, productSpecies i*(N i:ℝ)

theorem competition_covalent_balance (N : Counts) (V eps k r delta : ℝ) :
    competitionGenerator N V eps k r delta covalentCount +
      (∑ j,competitionRate N V eps k r delta j*competitionExport j) =
    4*((eps+delta*eps/16)*(N 0)*(N 1)/V-(eps*k+delta)*(N 2)+
      20*(N 4)-20*k*(N 5)) := by
  simp only [competitionGenerator, covalentCount, competition_rated_linear_jump,
    product_stoich]
  simp only [Fintype.sum_sum_type, competitionRate, competitionBase, competitionExport]
  simp [Fin.sum_univ_succ, countRate, drivenRate_zero, drivenRate_one,
    drivenBase, basalMark, catalyticMark, exportMark]
  ring

theorem competition_export_intensity (N : Counts) (V eps k r delta : ℝ) :
    (∑ j,competitionRate N V eps k r delta j*competitionExport j) = covalentCount N := by
  simp [Fintype.sum_sum_type, competitionRate, competitionExport, covalentCount,
    Fin.sum_univ_succ, countRate, exportMark, productSpecies]
  ring

theorem competition_total_rate_bound (N : Counts) (V eps k r delta : ℝ)
    (hV : 0 < V) (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 0 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5)
    (hN : ∀ i, (N i:ℝ) ≤ (5/2)*V) :
    (∑ j,competitionRate N V eps k r delta j) ≤ 3000*V := by
  have hold := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 18))) =>
    channel_rate_bound N V eps k r hV heps heps1 hk hk1 hr hr1 hN j)
  have hdirect : delta*(N 2) ≤ (3/2)*V := by
    have hh := mul_le_mul hd1 (hN 2) (by positivity : 0 ≤ (N 2:ℝ)) (by norm_num)
    nlinarith
  have hcoef : 0 ≤ delta*eps/16 := by positivity
  have hcoef1 : delta*eps/16 ≤ 22 := by
    have hh := mul_le_mul hd1 heps1 heps (by norm_num)
    nlinarith
  have hreverse := bounded_bimolecular_rate (N 0) (N 1) V (delta*eps/16)
    hV (by positivity) (hN 0) (hN 1) hcoef hcoef1
  norm_num at hold
  simp only [Fintype.sum_sum_type, competitionRate]
  simp only [Fin.sum_univ_two, drivenRate_zero, drivenRate_one]
  linarith

end
end RandomViability.Binding

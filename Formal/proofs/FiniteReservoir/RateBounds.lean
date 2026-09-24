import proofs.FiniteReservoir.CountSource
import proofs.FiniteCopyReactor.MaterialModel

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

theorem rate_le_fixed (N : Counts) (V r alpha beta : ℝ) (hV : 0 < V)
    (hbox : RateBox alpha beta) (j : CompetitionChannel) :
    internalRate N V r alpha beta j ≤ competitionRate N V (1/500000000) (1/10) r (1/25) j := by
  cases j with
  | inl j => exact le_rfl
  | inr j =>
    fin_cases j
    · norm_num [internalRate,competitionRate,drivenRate_zero,drivenBase,countRate]
      exact mul_le_mul_of_nonneg_right hbox.alpha_upper (Nat.cast_nonneg _)
    · norm_num [internalRate,competitionRate,drivenRate_one,drivenBase,countRate]
      have h := mul_le_mul_of_nonneg_right hbox.beta_upper
        (show 0 ≤ (N 0:ℝ)*(N 1)/V by positivity)
      convert h using 1 <;> ring

theorem total_rate_bound (N : Counts) (V : ℕ) (r alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21)
    (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    (∑ j,internalRate N V r alpha beta j) ≤ 3000*(V:ℝ) := by
  apply (Finset.sum_le_sum (fun j _ => rate_le_fixed N V r alpha beta hV hbox j)).trans
  apply competition_total_rate_bound N V (1/500000000) (1/10) r (1/25) hV
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by linarith)
    (by norm_num) (by norm_num)
  intro i
  linarith [resource_count_cap N V hc i]

theorem count_gross_bound (N : Counts) (V : ℕ) (alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    alpha*(N 2)+beta*(N 0)*(N 1)/(V:ℝ) < (9/200)*(V:ℝ) := by
  have hn (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V hc i)
  have h := (gross_bound alpha beta ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
    hbox (by positivity) (by positivity) (by positivity) (hn 0) (hn 1) (hn 2)).2
  have hm := mul_lt_mul_of_pos_right h hV
  have he : (alpha*((N 2:ℝ)/V)+beta*((N 0:ℝ)/V)*((N 1:ℝ)/V))*(V:ℝ)=
      alpha*(N 2)+beta*(N 0)*(N 1)/(V:ℝ) := by field_simp
  rwa [he] at hm

theorem bath_rate_nonneg (s : State) (V r d R : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (hd : 0 ≤ d) (hR : 0 < R) (j : CompetitionChannel) :
    0 ≤ rate s V r d R j := by
  rw [rate_binding]
  apply internal_nonneg _ _ _ _ _ hV hr
  · unfold alpha; positivity
  · unfold beta; positivity

theorem bath_internal_support (s : State) (V r d R : ℝ) (j : CompetitionChannel)
    (h : rate s V r d R j ≠ 0) : ∀ i, reactants (competitionBase j) i ≤ s.1 i := by
  rw [rate_binding] at h
  exact internal_support s.1 V r _ _ j h

end
end FiniteReservoir

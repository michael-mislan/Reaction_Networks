import proofs.RandomViability.BindingCompetitionDisabledSource
import proofs.RandomViability.BindingCompetitionScaling

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def competitionDisabledCountKernel (V C : ℕ) (p : CompetitionRateBox) (hV : 0<(V:ℝ)) :=
  (competitionCountedModel C (competitionDisabledModel V p hV) competitionCreationLabel).uniformize
    (competitionClock V) (by exact_mod_cast competitionClock_pos V hV)
    (fun X => competition_disabled_total V p hV X.1)

theorem competition_disabled_creation_probability (V C : ℕ) (p : CompetitionRateBox)
    (hV : 100000000≤V) (hv : 0<(V:ℝ)) :
    (competitionDisabledCountKernel V C p hv).poissonized
      ((competitionClock V:ℝ≥0)*(500+⟨competitionDuration V,(Real.exp_pos _).le⟩))
      (FiniteKernel.eventIndicator {X | (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 <
        (competitionServiceCount 0 X.2:ℝ)}) (foodInitial V,fun _=>0) ≤
      Real.exp (-(V:ℝ)*(competitionWindowNumber V:ℝ)/25000) := by
  have hh := competition_counter_probability C (competitionDisabledModel V p hv) competitionCreationLabel
    0 1 (competitionDisabledLambda*(V:ℝ)) ((V:ℝ)*(competitionWindowNumber V:ℝ)/21000)
    (by norm_num) (by unfold competitionDisabledLambda; positivity)
    (competition_disabled_creation_rate V p hv) (competitionClock V)
    (500+⟨competitionDuration V,(Real.exp_pos _).le⟩)
    (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)
    (foodInitial V,fun _=>0)
  norm_num only [competitionCounterPotential,competitionServiceCount,Fin.ext_iff,ite_false,ite_true,Fin.val_zero,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one,NNReal.coe_add,NNReal.coe_ofNat] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  change -1*((V:ℝ)*(competitionWindowNumber V:ℝ)/21000)+competitionDisabledLambda*(V:ℝ)*(Real.exp 1-1)*(500+competitionDuration V) ≤ -(V:ℝ)*(competitionWindowNumber V:ℝ)/25000
  have ht := competition_windows_time_upper V hV
  have hn : 0 ≤ competitionDisabledLambda*(V:ℝ) := by unfold competitionDisabledLambda; positivity
  have he := mul_le_mul_of_nonneg_left (show Real.exp 1-1 ≤ (2:ℝ) by linarith [Real.exp_one_lt_three]) hn
  have hm := mul_le_mul_of_nonneg_right he (show 0≤500+competitionDuration V by have := (Real.exp_pos ((V:ℝ)/1000000)); unfold competitionDuration; positivity)
  have hw := mul_le_mul_of_nonneg_left ht (show 0≤2*competitionDisabledLambda*(V:ℝ) by unfold competitionDisabledLambda; positivity)
  have hp : 0≤(V:ℝ)*(competitionWindowNumber V:ℝ) := by positivity
  dsimp [competitionDisabledLambda] at hm hw ⊢
  nlinarith only [hm,hw,hp]

theorem competition_disabled_resource_generator (N : Counts) (V eps k r delta : ℝ) :
    (∑ j,competitionDisabledRate N V eps k r delta j*(resourcePotential V (competitionNext N j)-resourcePotential V N)) =
      literalGenerator N V eps k r (resourcePotential V) := by
  have ha := competition_resource_potential_generator N V eps k r delta
  have hb := disabled_resource_generator N V eps k r
  simp only [competitionGenerator,Fintype.sum_sum_type,competitionRate,competitionNext,competitionBase] at ha
  simp only [Fintype.sum_sum_type,competitionDisabledRate,competitionNext,competitionBase]
  change disabledGenerator N V eps k r (resourcePotential V)+_=_
  rw [hb]
  change literalGenerator N V eps k r (resourcePotential V)+_=_ at ha
  exact ha

theorem competition_disabled_resource_foster (V : ℕ) (p : CompetitionRateBox) (hv : 0<(V:ℝ)) (X : BoxCounts V) :
    (competitionDisabledModel V p hv).generator (fun Z=>resourcePotential V (boxCounts Z)) X ≤ 4*resourceSource V := by
  by_cases h : resourceGood (boxCounts X) V
  · have he : (competitionDisabledModel V p hv).generator (fun Z=>resourcePotential V (boxCounts Z)) X =
        literalGenerator (boxCounts X) V (1/500000000) (1/p.K) p.r (resourcePotential V) := by
      simp only [FiniteJumpModel.generator,competitionDisabledModel,if_pos h]
      have hh := competition_disabled_resource_generator (boxCounts X) V (1/500000000) (1/p.K) p.r p.delta
      rw [← hh]
      apply Finset.sum_congr rfl
      intro j _
      rw [boxNext_exact V X (competitionBase j) h]
      rfl
    rw [he]
    have hh := stopped_resource_foster V (1/500000000) (1/p.K) p.r hv (by norm_num) (by norm_num)
      p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper X
    rw [stopped_generator_inside V (1/500000000) (1/p.K) p.r hv (by norm_num) p.inv_nonneg p.r_nonneg X _ h] at hh
    exact hh
  · simp only [FiniteJumpModel.generator,competitionDisabledModel,if_neg h,zero_mul,Finset.sum_const_zero]
    unfold resourceSource
    positivity

theorem competition_disabled_resource_probability (V : ℕ) (p : CompetitionRateBox) (hv : 0<(V:ℝ)) (t : ℝ≥0) :
    ((competitionDisabledModel V p hv).uniformize (competitionClock V)
      (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)).poissonized
      ((competitionClock V:ℝ≥0)*t) (FiniteKernel.eventIndicator {X | ¬resourceGood (boxCounts X) V}) (foodInitial V) ≤
      resourcePotential V (boxCounts (foodInitial V))+(t:ℝ)*(4*resourceSource V) := by
  have hh := (competitionDisabledModel V p hv).uniformized_event_bound (competitionClock V) t
    (by exact_mod_cast competitionClock_pos V hv) (competition_disabled_total V p hv)
    {X | ¬resourceGood (boxCounts X) V} (fun X=>resourcePotential V (boxCounts X)) 1 (4*resourceSource V)
    (fun X=>resourcePotential_nonneg V (boxCounts X))
    (fun X hX=>resourcePotential_exit V (boxCounts X) hX)
    (competition_disabled_resource_foster V p hv) (foodInitial V)
  simpa only [one_mul] using hh

theorem competition_disabled_export_requires_creation (V : ℕ) (hV : 100000000≤V)
    (js : List CompetitionChannel) (hs : competitionFeasibleTrace (boxCounts (foodInitial V)) js)
    (hj : ∀ j ∈ js,j ≠ Sum.inl 6 ∧ j ≠ Sum.inl 7)
    (he : (V:ℝ)*(competitionWindowNumber V:ℝ)/5000 ≤ ((js.map competitionExportUnits).sum:ℝ)) :
    (V:ℝ)*(competitionWindowNumber V:ℝ)/21000 < ((js.map competitionCreationMark).sum:ℝ) := by
  have hh := competition_disabled_inventory_history (boxCounts (foodInitial V)) js hs hj
  have hz : countProduct (boxCounts (foodInitial V))=0 := by simp [countProduct,productSpecies,boxCounts,foodInitial,Fin.sum_univ_succ]
  rw [hz] at hh
  have hn := countProduct_nonneg (js.foldl competitionNext (boxCounts (foodInitial V)))
  have hw := competition_windows_time_lower V hV
  have hd := competition_duration_large V hV
  have hv : 0<(V:ℝ) := by
    have hvv : (100000000:ℝ)≤V := by exact_mod_cast hV
    linarith
  have hm : 0<(V:ℝ)*(competitionWindowNumber V:ℝ) := mul_pos hv (by linarith)
  linarith

end
end RandomViability.Binding

import proofs.RandomViability.BindingDisabledChannels
import proofs.RandomViability.BindingCompetitionThroughput
import proofs.RandomViability.BindingCompetitionContractModel
import proofs.RandomViability.BindingCompetitionCounterProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped BigOperators NNReal

def competitionDisabledRate (N : Counts) (V eps k r delta : ℝ) : CompetitionChannel → ℝ
  | .inl j => disabledRate N V eps k r j
  | .inr j => drivenRate N V eps delta j

def competitionCreationMark : CompetitionChannel → ℕ
  | .inl j => if j=0 then 1 else 0
  | .inr j => if j=1 then 1 else 0

def competitionCreationLabel (j : CompetitionChannel) : Option (Fin 4) :=
  if competitionCreationMark j=1 then some 0 else none

theorem competition_creation_label (j : CompetitionChannel) :
    competitionServiceIncrement 0 (competitionCreationLabel j)=competitionCreationMark j := by
  cases j with
  | inl j => fin_cases j <;> norm_num [competitionCreationMark,competitionCreationLabel,competitionServiceIncrement,Fin.ext_iff]
  | inr j => fin_cases j <;> norm_num [competitionCreationMark,competitionCreationLabel,competitionServiceIncrement,Fin.ext_iff]

theorem competition_disabled_nonneg (N : Counts) (V : ℕ) (p : CompetitionRateBox)
    (hV : 0<(V:ℝ)) (j : CompetitionChannel) :
    0 ≤ competitionDisabledRate N V (1/500000000) (1/p.K) p.r p.delta j := by
  cases j with
  | inl j => exact disabledRate_nonneg N V _ _ _ hV (by norm_num) p.inv_nonneg p.r_nonneg j
  | inr j => exact competitionRate_nonneg N V _ _ _ _ hV (by norm_num) p.inv_nonneg p.r_nonneg p.delta_nonneg (.inr j)

theorem competition_disabled_le (N : Counts) (V : ℕ) (p : CompetitionRateBox)
    (hV : 0<(V:ℝ)) (j : CompetitionChannel) :
    competitionDisabledRate N V (1/500000000) (1/p.K) p.r p.delta j ≤
      competitionRate N V (1/500000000) (1/p.K) p.r p.delta j := by
  cases j with
  | inl j => exact disabledRate_le N V _ _ _ hV (by norm_num) p.inv_nonneg p.r_nonneg j
  | inr j => rfl

theorem competition_disabled_covalent_balance (N : Counts) (V eps k r delta : ℝ) :
    (∑ j,competitionDisabledRate N V eps k r delta j*
      (countProduct (competitionNext N j)-countProduct N+competitionExport j)) =
      4*((eps+delta*eps/16)*(N 0)*(N 1)/V-(eps*k+delta)*(N 2)) := by
  have hid (j : CompetitionChannel) : competitionDisabledRate N V eps k r delta j*
      (countProduct (competitionNext N j)-countProduct N+competitionExport j) =
      competitionDisabledRate N V eps k r delta j*(basalMark (competitionBase j)+catalyticMark (competitionBase j)) := by
    cases j with
    | inl j =>
      simp only [competitionDisabledRate,disabledRate]
      split_ifs
      · simp
      · have hh := rated_product_change N V eps k r j
        change countRate N V eps k r j*(countProduct (countNext N j)-countProduct N+exportMark j)=countRate N V eps k r j*(basalMark j+catalyticMark j)
        nlinarith only [hh]
    | inr j =>
      have hh := rated_product_change N V (if j=0 then delta else delta*eps/16) 1 0 (drivenBase j)
      have hz : exportMark (drivenBase j)=0 := by fin_cases j <;> norm_num [drivenBase,exportMark]
      rw [hz] at hh
      change drivenRate N V eps delta j*(countProduct (countNext N (drivenBase j))-countProduct N+0)=_
      simpa only [drivenRate,competitionDisabledRate,competitionBase,add_zero,sub_zero] using hh
  have ho := disabled_covalent_balance N V eps k r
  simp only [Fintype.sum_sum_type,competitionDisabledRate,competitionNext,competitionBase,competitionExport]
  rw [ho]
  have hd : (∑ j:Fin 2,drivenRate N V eps delta j*(countProduct (countNext N (drivenBase j))-countProduct N+0)) =
      4*(delta*eps/16*(N 0)*(N 1)/V-delta*(N 2)) := by
    have hh (j : Fin 2) := hid (Sum.inr j)
    simp only [competitionDisabledRate,competitionNext,competitionBase,competitionExport] at hh
    simp only [hh,Fin.sum_univ_two,drivenRate_zero,drivenRate_one]
    norm_num [drivenBase,basalMark,catalyticMark]
    ring
  rw [hd]
  ring

theorem competition_disabled_inventory_step (N : Counts) (j : CompetitionChannel)
    (hs : ∀ i,reactants (competitionBase j) i ≤ N i)
    (hj : j ≠ Sum.inl 6 ∧ j ≠ Sum.inl 7) :
    countProduct (competitionNext N j)-countProduct N+(competitionExportUnits j:ℝ) ≤
      4*(competitionCreationMark j:ℝ) := by
  have hh := next_linear_difference N (competitionBase j) productSpecies hs
  rw [product_stoich] at hh
  change countProduct (competitionNext N j)-countProduct N=_ at hh
  rw [hh,competitionExportUnits_real]
  cases j with
  | inl j => fin_cases j <;> simp_all [competitionBase,competitionExport,exportMark,basalMark,catalyticMark,competitionCreationMark,Fin.ext_iff]
  | inr j => fin_cases j <;> norm_num [competitionBase,competitionExport,exportMark,basalMark,catalyticMark,competitionCreationMark,drivenBase,Fin.ext_iff]

theorem competition_disabled_inventory_history (N : Counts) (js : List CompetitionChannel)
    (hs : competitionFeasibleTrace N js)
    (hj : ∀ j ∈ js,j ≠ Sum.inl 6 ∧ j ≠ Sum.inl 7) :
    countProduct (js.foldl competitionNext N)+((js.map competitionExportUnits).sum:ℝ) ≤
      countProduct N+4*((js.map competitionCreationMark).sum:ℝ) := by
  induction js generalizing N with
  | nil => simp
  | cons j js ih =>
    have hh := ih (competitionNext N j) hs.2 (fun k hk => hj k (by simp [hk]))
    have hm := competition_disabled_inventory_step N j hs.1 (hj j (by simp))
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,Nat.cast_add]
    linarith

def competitionDisabledModel (V : ℕ) (p : CompetitionRateBox) (hV : 0<(V:ℝ)) :
    FiniteJumpModel (BoxCounts V) CompetitionChannel where
  next X j := boxNext V X (competitionBase j)
  rate X j := if resourceGood (boxCounts X) V then competitionDisabledRate (boxCounts X) V (1/500000000) (1/p.K) p.r p.delta j else 0
  nonneg X j := by split_ifs; exact competition_disabled_nonneg _ V p hV j; rfl

theorem competition_disabled_total (V : ℕ) (p : CompetitionRateBox) (hV : 0<(V:ℝ)) (X : BoxCounts V) :
    (competitionDisabledModel V p hV).total X ≤ (competitionClock V:ℝ) := by
  by_cases h : resourceGood (boxCounts X) V
  · simp only [FiniteJumpModel.total,competitionDisabledModel,if_pos h]
    apply (Finset.sum_le_sum (fun j _ => competition_disabled_le _ V p hV j)).trans
    have hh := competition_total_rate_bound (boxCounts X) V (1/500000000) (1/p.K) p.r p.delta hV
      (by norm_num) (by norm_num) p.inv_nonneg p.inv_upper p.r_nonneg p.r_upper p.delta_nonneg p.delta_local (by
        intro i
        have hi := resource_count_cap (boxCounts X) V h i
        linarith)
    simpa only [competitionClock,Nat.cast_mul,Nat.cast_ofNat] using hh
  · simp [FiniteJumpModel.total,competitionDisabledModel,h,competitionClock]

def competitionDisabledLambda : ℝ := 38841/16000000000000

theorem competition_disabled_creation_rate (V : ℕ) (p : CompetitionRateBox) (hV : 0<(V:ℝ)) (X : BoxCounts V) :
    (∑ j,(competitionDisabledModel V p hV).rate X j*(competitionServiceIncrement 0 (competitionCreationLabel j):ℝ)) ≤
      competitionDisabledLambda*(V:ℝ) := by
  by_cases h : resourceGood (boxCounts X) V
  · simp only [competition_creation_label,competitionDisabledModel,if_pos h,Fintype.sum_sum_type]
    have hu := resource_count_cap (boxCounts X) V h 0
    have hw := resource_count_cap (boxCounts X) V h 1
    have hp := mul_le_mul hu hw (Nat.cast_nonneg (α := ℝ) (boxCounts X 1)) (by positivity : (0:ℝ)≤(11/10)*(V:ℝ))
    have hd := div_le_div_of_nonneg_right hp hV.le
    have he : ((11/10)*(V:ℝ)*((11/10)*(V:ℝ)))/(V:ℝ)=(121/100)*(V:ℝ) := by field_simp; ring
    rw [he] at hd
    have hc : (1/500000000:ℝ)+p.delta*(1/500000000)/16 ≤ 321/160000000000 := by have := p.delta_upper; linarith
    have hm := mul_le_mul hc hd (by positivity : 0≤(boxCounts X 0:ℝ)*(boxCounts X 1)/(V:ℝ)) (by norm_num : (0:ℝ)≤321/160000000000)
    simp only [competitionCreationMark,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_ite,mul_one,mul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,competitionDisabledRate]
    norm_num [disabledRate,countRate,drivenRate_one,Fin.ext_iff]
    dsimp [competitionDisabledLambda]
    convert hm using 1 <;> ring
  · simp [competitionDisabledModel,h,competitionDisabledLambda]

end
end RandomViability.Binding

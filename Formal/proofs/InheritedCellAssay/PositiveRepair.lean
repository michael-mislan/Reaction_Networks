import proofs.InheritedCellAssay.PositiveLaw

/-!
# Repaired prediction interval at the chronological process level

The count-threshold source law (`CountThresholdSource`) showed that the
prediction interval "total count at most two" fails, while "at most three"
succeeds, for the *observed* birth-only law. Here the "at most three" bound is
proved for the actual chronological positive-switching process. The route is the
one already compiled for the failure event: a finite killed model is
transported to the unrestricted trajectory law through the stopped clock.

* Resistant founder `(0,1)`: reuse `PositiveKilled.source` with the payoff
  "alive in live count one through three".
* Sensitive founder `(1,0)`: a new three-state killed model whose live set is
  `{(1,0),(0,0)}`; every live state has count at most one.
* Assembly: the mixture of the two endpoint measures of the count set
  `{x | x.1 + x.2 ≤ 3}` is at least `467880212635/481696324816 ≈ 0.9713`.
-/

namespace InheritedCellAssay.PositiveRepair
noncomputable section
open Classical FiniteCopy FiniteCopyReactor CompositionalMemory MeasureTheory
open InheritedCellAssay.PositiveTrajectory
open scoped ENNReal

/-! ### (A) Resistant founder: repaired payoff on the existing killed model -/

def repairPayoff (n : Fin 8) : ℝ := if n.val ≤ 2 then 1 else 0

theorem repairPayoff_bounds (n : Fin 8) : 0 ≤ repairPayoff n ∧ repairPayoff n ≤ 1 := by
  unfold repairPayoff
  split_ifs <;> norm_num

/-- Backward probability of being alive at live count one through three. -/
def repairValue (c t : ℝ) (n : Fin 8) : ℝ :=
  if n.val = 0 then (1*c^0) * (Real.exp (-t))^1 * (1-Real.exp (-t))^0 + (1*c^1) * (Real.exp (-t))^1 * (1-Real.exp (-t))^1 + (1*c^2) * (Real.exp (-t))^1 * (1-Real.exp (-t))^2 else
  if n.val = 1 then (1*c^0) * (Real.exp (-t))^2 * (1-Real.exp (-t))^0 + (2*c^1) * (Real.exp (-t))^2 * (1-Real.exp (-t))^1 else
  if n.val = 2 then (1*c^0) * (Real.exp (-t))^3 * (1-Real.exp (-t))^0 else 0

private theorem repair_backward_0 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => repairValue c s 0)
      ((PositiveKilled.source c hc hc1).generator (repairValue c t) 0) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : repairValue c t 7 = 0 := by rfl
  simp [PositiveKilled.source, PositiveKilled.next, FiniteJumpModel.generator, h7]
  convert (((((he.pow 1).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 1).const_mul (1*c^1)).mul (hh.pow 1))).add (((he.pow 1).const_mul (1*c^2)).mul (hh.pow 2))) using 1
  all_goals first
  | (solve | rfl)
  | (solve | norm_num [repairValue, Fin.isValue])
  | (norm_num [repairValue, Fin.isValue]; ring)

private theorem repair_backward_1 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => repairValue c s 1)
      ((PositiveKilled.source c hc hc1).generator (repairValue c t) 1) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : repairValue c t 7 = 0 := by rfl
  simp [PositiveKilled.source, PositiveKilled.next, FiniteJumpModel.generator, h7]
  convert ((((he.pow 2).const_mul (1*c^0)).mul (hh.pow 0)).add (((he.pow 2).const_mul (2*c^1)).mul (hh.pow 1))) using 1
  all_goals first
  | (solve | rfl)
  | (solve | norm_num [repairValue, Fin.isValue])
  | (norm_num [repairValue, Fin.isValue]; ring)

private theorem repair_backward_2 (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) :
    HasDerivAt (fun s => repairValue c s 2)
      ((PositiveKilled.source c hc hc1).generator (repairValue c t) 2) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hh := he.const_sub 1
  have h7 : repairValue c t 7 = 0 := by rfl
  simp [PositiveKilled.source, PositiveKilled.next, FiniteJumpModel.generator, h7]
  convert (((he.pow 3).const_mul (1*c^0)).mul (hh.pow 0)) using 1
  all_goals first
  | (solve | rfl)
  | (solve | norm_num [repairValue, Fin.isValue])
  | (norm_num [repairValue, Fin.isValue]; ring)

private theorem repairValue_dead (c t : ℝ) (n : Fin 8) (hn : 3 ≤ n.val) :
    repairValue c t n = 0 := by
  have h0 : n.val ≠ 0 := by omega
  have h1 : n.val ≠ 1 := by omega
  have h2 : n.val ≠ 2 := by omega
  simp [repairValue, h0, h1, h2]

private theorem next_true_dead (n : Fin 8) (hn : 3 ≤ n.val) :
    3 ≤ (PositiveKilled.next n true).val := by
  show 3 ≤ min (n.val+1) 7
  omega

private theorem repair_backward_dead (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) (n : Fin 8)
    (hn : 3 ≤ n.val) :
    HasDerivAt (fun s => repairValue c s n)
      ((PositiveKilled.source c hc hc1).generator (repairValue c t) n) t := by
  have hf : (fun s => repairValue c s n) = fun _ => (0 : ℝ) :=
    funext fun s => repairValue_dead c s n hn
  have hT : repairValue c t (PositiveKilled.next n true) = 0 :=
    repairValue_dead c t _ (next_true_dead n hn)
  have hF : repairValue c t (PositiveKilled.next n false) = 0 := by
    show repairValue c t 7 = 0
    rfl
  have hg : (PositiveKilled.source c hc hc1).generator (repairValue c t) n = 0 := by
    simp only [FiniteJumpModel.generator, PositiveKilled.source, Fintype.sum_bool, hT, hF,
      repairValue_dead c t n hn]
    ring
  rw [hf, hg]
  exact hasDerivAt_const t (0 : ℝ)

theorem repair_backward (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (t : ℝ) (n : Fin 8) :
    HasDerivAt (fun s => repairValue c s n)
      ((PositiveKilled.source c hc hc1).generator (repairValue c t) n) t := by
  fin_cases n
  · exact repair_backward_0 c hc hc1 t
  · exact repair_backward_1 c hc hc1 t
  · exact repair_backward_2 c hc hc1 t
  all_goals exact repair_backward_dead c hc hc1 t _ (by decide)

/-- Exact finite killed value of the repaired event for the resistant founder. -/
theorem finite_repair_exact (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    finiteTimeExpectation (PositiveKilled.source c hc hc1) CountThreshold.horizon repairPayoff 0 =
      (1/2) * (1 + c/2 + (c/2)^2) := by
  have hv : repairPayoff = repairValue c 0 := by
    funext n
    fin_cases n <;> norm_num [repairPayoff, repairValue]
  rw [hv, CountThreshold.backward_solution_expectation _ _ (repair_backward c hc hc1)]
  change repairValue c (Real.log 2) 0 = _
  norm_num [repairValue, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  try ring

theorem finite_repair_value :
    finiteTimeExpectation finiteSource CountThreshold.horizon repairPayoff 0 =
      (1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2) :=
  finite_repair_exact (10000/10001) (by norm_num) (by norm_num)

/-- Success event: total count at most three. -/
def repairSuccess (x : State) : ℝ≥0∞ := if x.1 + x.2 ≤ 3 then 1 else 0

theorem repairSuccess_le_one (x : State) : repairSuccess x ≤ 1 := by
  unfold repairSuccess
  split_ifs <;> norm_num

theorem observed_repair (x : State) :
    ENNReal.ofReal (repairPayoff (observe x)) = if x ∈ live then repairSuccess x else 0 := by
  by_cases hx : x ∈ live
  · have hs := hx.1
    have hl := hx.2.1
    have hh := hx.2.2
    simp only [observe, dif_pos hx, repairPayoff, Fin.val_mk, if_pos hx, repairSuccess, hs,
      zero_add]
    by_cases h3 : x.2 ≤ 3
    · have he : x.2-1 ≤ 2 := by omega
      simp [he, h3]
    · have he : ¬ (x.2-1 ≤ 2) := by omega
      simp only [if_neg he, ENNReal.ofReal_zero, if_neg h3]
  · norm_num [observe, hx, repairPayoff]

theorem resistant_le_actual :
    ENNReal.ofReal (finiteTimeExpectation finiteSource CountThreshold.horizon repairPayoff 0) ≤
      chronologicalEndpoint next rate rate_nonneg total_pos repairSuccess (0,1)
        CountThreshold.horizon := by
  have hp := clock_finite_projection stopped finiteSource observe (8 : NNReal)
    CountThreshold.horizon (by norm_num) finite_bound step_projection repairPayoff
    repairPayoff_bounds (0,1)
  have ho : observe (0,1) = 0 := by norm_num [observe, live]
  rw [ho] at hp
  have hc : causalClockEndpoint stopped 8
      (fun y => if y ∈ live then repairSuccess y else 0) (0,1) CountThreshold.horizon =
      ENNReal.ofReal (finiteTimeExpectation finiteSource CountThreshold.horizon repairPayoff 0) := by
    unfold causalClockEndpoint
    split_ifs with ht
    · simpa only [observed_repair] using hp
    · exact (ht CountThreshold.horizon.property).elim
  rw [← hc]
  exact stopped_clock_le_unrestricted live next rate rate_nonneg total_pos 8
    (by norm_num) live_bound repairSuccess repairSuccess_le_one (0,1) _

/-! ### (B) Sensitive founder: a three-state killed model -/

/-- Live set for the sensitive founder: `(1,0)` and `(0,0)`. -/
def liveS : Set State := {x | x.2 = 0 ∧ x.1 ≤ 1}

theorem liveS_bound (x : State) (hx : x ∈ liveS) : (∑ b, rate x b) ≤ 5 := by
  rw [total_eq, hx.1]
  have h : (x.1 : ℝ) ≤ 1 := by exact_mod_cast hx.2
  linarith

/-- State `0` is `(1,0)`, state `1` is `(0,0)`, state `2` is the cemetery. -/
def observeS (x : State) : Fin 3 :=
  if x = (1,0) then 0 else if x = (0,0) then 1 else 2

theorem observeS_dead (x : State) (hx : x ∉ liveS) : observeS x = 2 := by
  have h1 : x ≠ (1,0) := by
    rintro rfl
    exact hx (by simp [liveS])
  have h2 : x ≠ (0,0) := by
    rintro rfl
    exact hx (by simp [liveS])
  simp [observeS, h1, h2]

def sensitiveNext (n : Fin 3) (b : Bool) : Fin 3 :=
  if n.val = 0 then (if b then 1 else 2) else n

def sensitiveRate (n : Fin 3) (b : Bool) : ℝ :=
  if n.val = 0 then (if b then 30000/10001 else 100/10001) else 0

def sensitiveSource : FiniteJumpModel (Fin 3) Bool where
  next := sensitiveNext
  rate := sensitiveRate
  nonneg n b := by
    unfold sensitiveRate
    split_ifs <;> norm_num

private theorem sNext_0_true : sensitiveNext 0 true = 1 := rfl
private theorem sNext_0_false : sensitiveNext 0 false = 2 := rfl
private theorem sNext_1 (b : Bool) : sensitiveNext 1 b = 1 := rfl
private theorem sNext_2 (b : Bool) : sensitiveNext 2 b = 2 := rfl
private theorem sRate_0_true : sensitiveRate 0 true = 30000/10001 := rfl
private theorem sRate_0_false : sensitiveRate 0 false = 100/10001 := rfl
private theorem sRate_1 (b : Bool) : sensitiveRate 1 b = 0 := rfl
private theorem sRate_2 (b : Bool) : sensitiveRate 2 b = 0 := rfl

private theorem generator_0 (v : Fin 3 → ℝ) :
    sensitiveSource.generator v 0 = 30000/10001 * (v 1 - v 0) + 100/10001 * (v 2 - v 0) := by
  simp only [FiniteJumpModel.generator, sensitiveSource, Fintype.sum_bool, sNext_0_true,
    sNext_0_false, sRate_0_true, sRate_0_false]

private theorem generator_1 (v : Fin 3 → ℝ) : sensitiveSource.generator v 1 = 0 := by
  simp [FiniteJumpModel.generator, sensitiveSource, sRate_1]

private theorem generator_2 (v : Fin 3 → ℝ) : sensitiveSource.generator v 2 = 0 := by
  simp [FiniteJumpModel.generator, sensitiveSource, sRate_2]

theorem sensitive_bound (n : Fin 3) : sensitiveSource.total n ≤ 5 := by
  fin_cases n
  · show sensitiveSource.total 0 ≤ 5
    norm_num [FiniteJumpModel.total, sensitiveSource, Fintype.sum_bool, sRate_0_true, sRate_0_false]
  · show sensitiveSource.total 1 ≤ 5
    norm_num [FiniteJumpModel.total, sensitiveSource, Fintype.sum_bool, sRate_1]
  · show sensitiveSource.total 2 ≤ 5
    norm_num [FiniteJumpModel.total, sensitiveSource, Fintype.sum_bool, sRate_2]

def stoppedS := stoppedClockKernel liveS next rate rate_nonneg 5 (by norm_num) liveS_bound

/-- The exact stopped process on the sensitive live set has the same observed
    transition as the three-state killed model. -/
theorem stepS_projection (g : Fin 3 → ℝ) (x : State) :
    (∑ b, stoppedS.prob x b * g (observeS (stoppedS.next x b))) =
      (sensitiveSource.uniformize 5 (by norm_num) sensitive_bound).step g (observeS x) := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases hx : x ∈ liveS
  · rcases x with ⟨s,r⟩
    have hr : r = 0 := hx.1
    have hs : s ≤ 1 := hx.2
    subst hr
    interval_cases s <;>
      norm_num [stoppedS, stoppedClockKernel, boundedClockKernel, stoppedRate,
        Fintype.sum_option, Fin.sum_univ_succ, liveS, next, rate, observeS,
        generator_0, generator_1] <;> ring
  · have ho := observeS_dead x hx
    simp [stoppedS, stoppedClockKernel, boundedClockKernel, stoppedRate, hx,
      Fintype.sum_option, ho, generator_2]

def sensitivePayoff (n : Fin 3) : ℝ := if n.val ≤ 1 then 1 else 0

theorem sensitivePayoff_bounds (n : Fin 3) : 0 ≤ sensitivePayoff n ∧ sensitivePayoff n ≤ 1 := by
  unfold sensitivePayoff
  split_ifs <;> norm_num

private theorem sPayoff_0 : sensitivePayoff 0 = 1 := rfl
private theorem sPayoff_1 : sensitivePayoff 1 = 1 := rfl
private theorem sPayoff_2 : sensitivePayoff 2 = 0 := rfl

theorem observedS_payoff (x : State) :
    ENNReal.ofReal (sensitivePayoff (observeS x)) = if x ∈ liveS then repairSuccess x else 0 := by
  by_cases hx : x ∈ liveS
  · rcases x with ⟨s,r⟩
    have hr : r = 0 := hx.1
    have hs : s ≤ 1 := hx.2
    subst hr
    rw [if_pos hx]
    interval_cases s <;> simp [observeS, sPayoff_0, sPayoff_1, repairSuccess]
  · rw [if_neg hx, observeS_dead x hx, sPayoff_2]
    simp

/-- Backward value: `exp(-k t) + (300/301)(1 - exp(-k t))` at the sensitive founder. -/
def sensitiveValue (t : ℝ) (n : Fin 3) : ℝ :=
  if n.val = 0 then (1/301) * Real.exp (-(30100/10001 * t)) + 300/301
  else if n.val = 1 then 1 else 0

private theorem sValue_0 (t : ℝ) :
    sensitiveValue t 0 = (1/301) * Real.exp (-(30100/10001 * t)) + 300/301 := rfl
private theorem sValue_1 (t : ℝ) : sensitiveValue t 1 = 1 := rfl
private theorem sValue_2 (t : ℝ) : sensitiveValue t 2 = 0 := rfl

theorem sensitive_backward (t : ℝ) (n : Fin 3) :
    HasDerivAt (fun s => sensitiveValue s n) (sensitiveSource.generator (sensitiveValue t) n) t := by
  fin_cases n
  · show HasDerivAt (fun s => sensitiveValue s 0) (sensitiveSource.generator (sensitiveValue t) 0) t
    have hf : (fun s => sensitiveValue s 0) =
        fun s => (1/301) * Real.exp (-(30100/10001 * s)) + 300/301 :=
      funext fun s => sValue_0 s
    have h1 : HasDerivAt (fun s : ℝ => 30100/10001 * s) (30100/10001 * 1) t :=
      (hasDerivAt_id t).const_mul _
    have he : HasDerivAt (fun s : ℝ => Real.exp (-(30100/10001 * s)))
        (Real.exp (-(30100/10001 * t)) * -(30100/10001 * 1)) t := h1.neg.exp
    rw [hf, generator_0, sValue_0, sValue_1, sValue_2]
    convert (he.const_mul (1/301 : ℝ)).add_const (300/301 : ℝ) using 1
    all_goals first
    | rfl
    | ring
  · show HasDerivAt (fun s => sensitiveValue s 1) (sensitiveSource.generator (sensitiveValue t) 1) t
    rw [generator_1, show (fun s => sensitiveValue s 1) = fun _ => (1 : ℝ) from
      funext fun s => sValue_1 s]
    exact hasDerivAt_const t (1 : ℝ)
  · show HasDerivAt (fun s => sensitiveValue s 2) (sensitiveSource.generator (sensitiveValue t) 2) t
    rw [generator_2, show (fun s => sensitiveValue s 2) = fun _ => (0 : ℝ) from
      funext fun s => sValue_2 s]
    exact hasDerivAt_const t (0 : ℝ)

theorem finite_sensitive_exact :
    finiteTimeExpectation sensitiveSource CountThreshold.horizon sensitivePayoff 0 =
      (1/301) * Real.exp (-(30100/10001 * Real.log 2)) + 300/301 := by
  have hv : sensitivePayoff = sensitiveValue 0 := by
    funext n
    fin_cases n
    · show sensitivePayoff 0 = sensitiveValue 0 0
      rw [sPayoff_0, sValue_0]
      norm_num
    · show sensitivePayoff 1 = sensitiveValue 0 1
      rfl
    · show sensitivePayoff 2 = sensitiveValue 0 2
      rfl
  rw [hv, CountThreshold.backward_solution_expectation _ _ sensitive_backward]
  exact sValue_0 (Real.log 2)

theorem finite_sensitive_ge :
    (300/301 : ℝ) ≤ finiteTimeExpectation sensitiveSource CountThreshold.horizon sensitivePayoff 0 := by
  rw [finite_sensitive_exact]
  have := Real.exp_pos (-(30100/10001 * Real.log 2))
  linarith

theorem sensitive_le_actual :
    ENNReal.ofReal (finiteTimeExpectation sensitiveSource CountThreshold.horizon sensitivePayoff 0) ≤
      chronologicalEndpoint next rate rate_nonneg total_pos repairSuccess (1,0)
        CountThreshold.horizon := by
  have hp := clock_finite_projection stoppedS sensitiveSource observeS (5 : NNReal)
    CountThreshold.horizon (by norm_num) sensitive_bound stepS_projection sensitivePayoff
    sensitivePayoff_bounds (1,0)
  have ho : observeS (1,0) = 0 := by simp [observeS]
  rw [ho] at hp
  have hc : causalClockEndpoint stoppedS 5
      (fun y => if y ∈ liveS then repairSuccess y else 0) (1,0) CountThreshold.horizon =
      ENNReal.ofReal (finiteTimeExpectation sensitiveSource CountThreshold.horizon
        sensitivePayoff 0) := by
    unfold causalClockEndpoint
    split_ifs with ht
    · simpa only [observedS_payoff] using hp
    · exact (ht CountThreshold.horizon.property).elim
  rw [← hc]
  exact stopped_clock_le_unrestricted liveS next rate rate_nonneg total_pos 5
    (by norm_num) liveS_bound repairSuccess repairSuccess_le_one (1,0) _

/-! ### (C) Assembly at the level of the endpoint probability measures -/

def countSuccessSet : Set State := {x | x.1 + x.2 ≤ 3}

theorem success_eq_probability (x : State) :
    chronologicalEndpoint next rate rate_nonneg total_pos repairSuccess x CountThreshold.horizon =
      chronologicalMeasure next rate rate_nonneg total_pos x CountThreshold.horizon
        countSuccessSet := by
  rw [chronological_endpoint_measure next rate rate_nonneg total_pos x
    CountThreshold.horizon CountThreshold.horizon.property (source_nonexplosion x)]
  have hf : repairSuccess = countSuccessSet.indicator (fun _ => 1) := by
    funext y
    simp [repairSuccess, countSuccessSet, Set.indicator]
  rw [hf, lintegral_indicator (Set.to_countable countSuccessSet).measurableSet]
  simp

/-- Actual probability, under the stated founder mixture, that the total count at
    the horizon is at most three. -/
def mixtureSuccess : ℝ≥0∞ :=
  ENNReal.ofReal (19/24 : ℝ) *
    chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
      countSuccessSet +
  ENNReal.ofReal (5/24 : ℝ) *
    chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
      countSuccessSet

/-- The repaired prediction interval "at most three" covers the actual
    chronological process with probability at least `467880212635/481696324816`,
    about `0.9713`, which exceeds the nominal `19/20`. -/
theorem actual_repair_probability_ge :
    ENNReal.ofReal (467880212635/481696324816 : ℝ) ≤ mixtureSuccess := by
  have hA : ENNReal.ofReal ((1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2)) ≤
      chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
        countSuccessSet := by
    have h1 := resistant_le_actual
    rw [finite_repair_value, success_eq_probability] at h1
    exact h1
  have hB : ENNReal.ofReal (300/301 : ℝ) ≤
      chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
        countSuccessSet := by
    have h1 := sensitive_le_actual
    rw [success_eq_probability] at h1
    exact (ENNReal.ofReal_le_ofReal finite_sensitive_ge).trans h1
  have hV : (0 : ℝ) ≤ (1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2) := by norm_num
  have e1 : ENNReal.ofReal ((19/24 : ℝ) * (300/301)) =
      ENNReal.ofReal (19/24 : ℝ) * ENNReal.ofReal (300/301 : ℝ) :=
    ENNReal.ofReal_mul (by norm_num)
  have e2 : ENNReal.ofReal ((5/24 : ℝ) * ((1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2))) =
      ENNReal.ofReal (5/24 : ℝ) *
        ENNReal.ofReal ((1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2)) :=
    ENNReal.ofReal_mul (by norm_num)
  calc ENNReal.ofReal (467880212635/481696324816 : ℝ)
      = ENNReal.ofReal ((19/24 : ℝ) * (300/301) +
          (5/24 : ℝ) * ((1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2))) := by
        congr 1
        norm_num
    _ = ENNReal.ofReal (19/24 : ℝ) * ENNReal.ofReal (300/301 : ℝ) +
        ENNReal.ofReal (5/24 : ℝ) *
          ENNReal.ofReal ((1/2) * (1 + (10000/10001)/2 + ((10000/10001)/2)^2)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), e1, e2]
    _ ≤ mixtureSuccess := add_le_add (mul_le_mul_right hB _) (mul_le_mul_right hA _)

/-! ### (D) Two consequences -/

/-- The exact finite killed value gives the failure probability lower bound
    `151415045117539070312500/3001800450060004500180003 ≈ 0.05044`. -/
theorem actual_failure_ge_exact :
    ENNReal.ofReal (151415045117539070312500/3001800450060004500180003 : ℝ) ≤ mixtureFailure := by
  have hf : finiteTimeExpectation finiteSource CountThreshold.horizon payoff 0 =
      (1/2) * (((10000/10001)/2)^2+((10000/10001)/2)^3+((10000/10001)/2)^4+
        ((10000/10001)/2)^5+((10000/10001)/2)^6) :=
    PositiveKilled.finite_failure_exact (10000/10001) (by norm_num) (by norm_num)
  have h1 := mul_le_mul_right finite_le_actual (ENNReal.ofReal (5/24 : ℝ))
  rw [hf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5/24)] at h1
  calc ENNReal.ofReal (151415045117539070312500/3001800450060004500180003 : ℝ)
      = ENNReal.ofReal ((5/24 : ℝ) * ((1/2) * (((10000/10001)/2)^2+((10000/10001)/2)^3+
          ((10000/10001)/2)^4+((10000/10001)/2)^5+((10000/10001)/2)^6))) := by
        congr 1
        norm_num
    _ ≤ mixtureFailure := h1.trans (le_add_left le_rfl)

def countSuccessSet2 : Set State := {x | x.1 + x.2 ≤ 2}

theorem countSuccessSet2_eq : countSuccessSet2 = countFailureSetᶜ := by
  ext x
  simp only [countSuccessSet2, countFailureSet, Set.mem_compl_iff, Set.mem_setOf_eq]
  omega

/-- At the process level, the prediction interval "at most two" under-covers:
    its mixture probability is strictly below the nominal `19/20`. -/
theorem interval_two_undercovers :
    ENNReal.ofReal (19/24 : ℝ) *
      chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
        countSuccessSet2 +
    ENNReal.ofReal (5/24 : ℝ) *
      chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
        countSuccessSet2 <
    ENNReal.ofReal (19/20 : ℝ) := by
  have hgt := actual_count_probability_gt
  have e1 : chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
      countSuccessSet2 =
      1 - chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
        countFailureSet := by
    rw [countSuccessSet2_eq]
    exact prob_compl_eq_one_sub (Set.to_countable _).measurableSet
  have e2 : chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
      countSuccessSet2 =
      1 - chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
        countFailureSet := by
    rw [countSuccessSet2_eq]
    exact prob_compl_eq_one_sub (Set.to_countable _).measurableSet
  have ha1 : chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
      countFailureSet ≤ 1 := prob_le_one
  have hb1 : chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
      countFailureSet ≤ 1 := prob_le_one
  rw [e1, e2]
  set a := chronologicalMeasure next rate rate_nonneg total_pos (1,0) CountThreshold.horizon
    countFailureSet with ha
  set b := chronologicalMeasure next rate rate_nonneg total_pos (0,1) CountThreshold.horizon
    countFailureSet with hb
  have haT : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hbT : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb1
  have h19 : (0 : ℝ) ≤ 19/24 := by norm_num
  have h5 : (0 : ℝ) ≤ 5/24 := by norm_num
  have m1 : ENNReal.ofReal (19/24 : ℝ) * (1 - a) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have m2 : ENNReal.ofReal (5/24 : ℝ) * (1 - b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have n1 : ENNReal.ofReal (19/24 : ℝ) * a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top haT
  have n2 : ENNReal.ofReal (5/24 : ℝ) * b ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbT
  rw [ENNReal.lt_ofReal_iff_toReal_lt (ENNReal.add_ne_top.mpr ⟨m1, m2⟩), ENNReal.toReal_add m1 m2,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le ha1 ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le hb1 ENNReal.one_ne_top, ENNReal.toReal_ofReal h19,
    ENNReal.toReal_ofReal h5, ENNReal.toReal_one]
  have h' := ENNReal.toReal_strict_mono (ENNReal.add_ne_top.mpr ⟨n1, n2⟩) hgt
  rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/20), ENNReal.toReal_add n1 n2,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal h19,
    ENNReal.toReal_ofReal h5] at h'
  linarith

end
end InheritedCellAssay.PositiveRepair

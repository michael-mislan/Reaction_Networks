import proofs.LowFounderPrediction.Source

namespace LowFounderPrediction
noncomputable section
open Classical FiniteCopy CompositionalMemory HeritableCompositions

def c : ℝ := 9950/10051
def amax : ℝ := 10051/100000
def sensitiveLower : ℝ := 599/603

def value (t : ℝ) (n : Fin 6) : ℝ :=
  let e := Real.exp (-amax*t)
  if n.val = 0 then 1 else if n.val = 1 then sensitiveLower
  else if n.val = 2 then e+c*e*(1-e)+c^2*e*(1-e)^2
  else if n.val = 3 then e^2+2*c*e^2*(1-e)
  else if n.val = 4 then e^3 else 0

def dv (t : ℝ) (n : Fin 6) : ℝ :=
  if n.val = 2 then (199/2000)*value t 3-amax*value t 2
  else if n.val = 3 then 2*((199/2000)*value t 4-amax*value t 3)
  else if n.val = 4 then -3*amax*value t 4 else 0

theorem value_deriv (t : ℝ) (n : Fin 6) :
    HasDerivAt (fun u => value u n) (dv t n) t := by
  have he : HasDerivAt (fun u : ℝ => Real.exp (-amax*u))
      (-amax*Real.exp (-amax*t)) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-amax)).exp
  have hh := he.const_sub 1
  fin_cases n
  · simpa [value, dv] using (hasDerivAt_const t (1 : ℝ))
  · simpa [value, dv] using (hasDerivAt_const t sensitiveLower)
  · convert (he.add ((he.const_mul c).mul hh)).add
      ((he.const_mul (c^2)).mul (hh.pow 2)) using 1
    norm_num [value, dv, amax, c]
    ring
  · convert (he.pow 2).add ((((he.pow 2).const_mul (2*c))).mul hh) using 1
    norm_num [value, dv, amax, c]
    ring
  · convert he.pow 3 using 1
    norm_num [value, dv]
    ring
  · simpa [value, dv] using (hasDerivAt_const t (0 : ℝ))

theorem value_nonneg (t : ℝ) (ht : 0 ≤ t) (n : Fin 6) : 0 ≤ value t n := by
  have he : Real.exp (-amax*t) ≤ 1 := Real.exp_le_one_iff.mpr (by unfold amax; nlinarith)
  have hc : 0 ≤ c := by norm_num [c]
  have hs : 0 ≤ sensitiveLower := by norm_num [sensitiveLower]
  have hh : 0 ≤ 1-Real.exp (-amax*t) := by linarith
  unfold value
  split_ifs <;> positivity

/-- A rectangular relaxation of the guide's two L1 rate balls. -/
structure Admissible (a : Rates) : Prop where
  sensitive_total : a.bS+a.dS+a.qS ≤ 603/2000
  sensitive_death : 599/2000 ≤ a.dS
  resistant_total : a.bR+a.dR+a.qR ≤ amax
  resistant_birth : 199/2000 ≤ a.bR

set_option maxRecDepth 4096 in
theorem value_subsolution (a : Rates) (ha : Admissible a) (t : ℝ) (ht : 0 ≤ t)
    (n : Fin 6) : dv t n ≤ (killed a).generator (value t) n := by
  have hv := value_nonneg t ht
  have hbS := a.bS_nonneg; have hdS := a.dS_nonneg; have hqS := a.qS_nonneg
  have hbR := a.bR_nonneg; have hdR := a.dR_nonneg; have hqR := a.qR_nonneg
  have hs := ha.sensitive_total
  have hd := ha.sensitive_death
  have hr := ha.resistant_total
  have hb := ha.resistant_birth
  have hv0 : value t 0 = 1 := by simp [value]
  have hv1 : value t 1 = sensitiveLower := by simp [value]
  have hv5 : value t 5 = 0 := by simp [value]
  have hS : a.dS-(a.bS+a.dS+a.qS)*sensitiveLower ≥ 0 := by
    norm_num [sensitiveLower] at *
    linarith
  have hR (j : Fin 6) : (a.bR+a.dR+a.qR)*value t j ≤ amax*value t j :=
    mul_le_mul_of_nonneg_right hr (hv j)
  have hB (j : Fin 6) : (199/2000)*value t j ≤ a.bR*value t j :=
    mul_le_mul_of_nonneg_right hb (hv j)
  have hQ := mul_nonneg hqS (hv 2)
  have hD0 := mul_nonneg hdR (hv 0)
  have hD2 := mul_nonneg hdR (hv 2)
  have hD3 := mul_nonneg hdR (hv 3)
  have hQ1 := mul_nonneg hqR (hv 1)
  rw [hv0] at hD0
  rw [hv1] at hQ1
  fin_cases n <;>
    norm_num [FiniteJumpModel.generator, killed, repr, next, observe,
      rate, Fin.sum_univ_succ, Fin.isValue, dv, hv0, hv1, hv5]
  all_goals
    try rw [show value t (⟨2, by decide⟩ : Fin 6) = value t 2 from rfl]
    try rw [show value t (⟨3, by decide⟩ : Fin 6) = value t 3 from rfl]
    try rw [show value t (⟨4, by decide⟩ : Fin 6) = value t 4 from rfl]
  all_goals nlinarith [hR 2, hR 3, hR 4, hB 3, hB 4]

def payoff (n : Fin 6) : ℝ := if n.val = 5 then 0 else 1

theorem payoff_bounds (n : Fin 6) : 0 ≤ payoff n ∧ payoff n ≤ 1 := by
  unfold payoff
  split_ifs <;> norm_num

theorem initial_le_payoff (n : Fin 6) : value 0 n ≤ payoff n := by
  fin_cases n <;> norm_num [value, payoff, sensitiveLower]

theorem finite_lower (a : Rates) (ha : Admissible a) (T : NNReal) (n : Fin 6) :
    value T n ≤ finiteTimeExpectation (killed a) T payoff n := by
  let v := fun t y => -value ((T : ℝ)-t) y
  let d := fun t y => dv ((T : ℝ)-t) y
  have hd (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) T) (y : Fin 6) :
      HasDerivAt (fun u => v u y) (d t y) t := by
    have h := ((value_deriv ((T : ℝ)-t) y).comp t
      ((hasDerivAt_id t).const_sub (T : ℝ))).neg
    simpa [v, d] using h
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (y : Fin 6) :
      d t y+(killed a).generator (v t) y ≤ 0 := by
    have h := value_subsolution a ha ((T : ℝ)-t) (by linarith [ht.2]) y
    have he : (killed a).generator (v t) y =
        -(killed a).generator (value ((T : ℝ)-t)) y := by
      simp only [FiniteJumpModel.generator, v, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [he]
    exact sub_nonpos.mpr h
  have hh := finite_time_dependent_drift_bound (killed a) T v d 0 hd hg n
  have he : finiteTimeExpectation (killed a) T (v T) n =
      -finiteTimeExpectation (killed a) T (value 0) n := by
    simp [v, finiteTimeExpectation, Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
  rw [he] at hh
  have hl : value T n ≤ finiteTimeExpectation (killed a) T (value 0) n := by
    simpa [v] using (neg_le_neg_iff.mp (by simpa [v] using hh))
  obtain ⟨q,hq,_,hb⟩ := (killed a).exists_clock 0
  have hm := poisson_mono ((killed a).uniformize q hq hb) (q*T)
    (value 0) payoff initial_le_payoff n
  rw [← finite_time_eq_uniformized (killed a) q T hq hb,
    ← finite_time_eq_uniformized (killed a) q T hq hb] at hm
  exact hl.trans hm

end
end LowFounderPrediction

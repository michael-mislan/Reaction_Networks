import proofs.FiniteReservoir.RoundedService

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators NNReal

/-- Correlated bath fractions, rather than independent coefficient maxima. -/
theorem pure_gross_envelope (a b u w x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hw0 : 0 ≤ w)
    (hu : u ≤ 11/10) (hw : w ≤ 11/10) (hx : x ≤ 11/10) :
    (1/50)*(a*x+(1/8000000000)*b*u*w) ≤ 11/500 := by
  have huw := mul_le_mul hu hw hw0 (by norm_num : (0:ℝ) ≤ 11/10)
  have ht : (1/8000000000)*u*w ≤ (11/10:ℝ) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left ht hb
  nlinarith

/-- The rounding buffer used by the joint event still fits the old error allocation. -/
theorem sharp_rounded_exponent (V : ℝ) (hV : 1000000 ≤ V) :
    -(1/10)*(V/10-1)+4*(11/500)*V*(Real.exp (1/10)-1) ≤ -V/2000 := by
  have he := exp_small_quadratic (1/10:ℝ) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ V by linarith)
  nlinarith

theorem pure_count_gross (V R : ℕ) (hV : 0 < (V:ℝ)) (hR : 0 < (R:ℝ))
    (b : Bath) (ht : b.total=R) (N : Counts) (hc : resourceGood N V) :
    alpha b (1/50) R*(N 2)+beta b (1/50) R*(N 0)*(N 1)/(V:ℝ) ≤ (11/500)*(V:ℝ) := by
  have hab : (b.fuel:ℝ)/R+(b.waste:ℝ)/R=1 := by
    rw [← add_div]
    have he : (b.fuel:ℝ)+(b.waste:ℝ)=(R:ℝ) := by exact_mod_cast ht
    rw [he,div_self (ne_of_gt hR)]
  have hn (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V hc i)
  have hh := pure_gross_envelope ((b.fuel:ℝ)/R) ((b.waste:ℝ)/R)
    ((N 0:ℝ)/V) ((N 1:ℝ)/V) ((N 2:ℝ)/V)
    (by positivity) (by positivity) hab (by positivity) (hn 0) (hn 1) (hn 2)
  have hm := mul_le_mul_of_nonneg_right hh hV.le
  convert hm using 1
  dsimp [alpha,beta]
  field_simp

theorem pure_supply_cap (V R : ℕ) (p : Parameters R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : p.capacity=R) (hd : p.cleavage=1/50)
    (b : Bool) (N : BoxState V R) :
    (∑ j,(supplyModel b V R p hV).rate N j*supplyMark .gross j) ≤ (11/500)*(V:ℝ) := by
  have hlocal (active : Counts → Prop) (ha : ∀ X, active X → resourceGood X V) :
      (∑ j,(model V R p hV active).rate N j*supplyMark .gross j) ≤ (11/500)*(V:ℝ) := by
    by_cases hc : active (boxCounts N.1)
    · simp only [model,if_pos hc,rate_binding,boxState,gross_intensity]
      rw [hd,hcapacity]
      exact pure_count_gross V R hV hR _ (bathOf_total N.2) _ (ha _ hc)
    · simp only [model,if_neg hc,zero_mul,Finset.sum_const_zero]
      positivity
  cases b
  · exact hlocal (fun X => resourceGood X V) (fun _ h => h)
  · exact hlocal (fun X => resourceGood X V ∧ (V:ℝ)/20 < weightedCount X) (fun _ h => h.1)

/-- A general cap interface for the actual three-stage marked source. -/
theorem supply_cycle_cap (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ b (N : BoxState V M),
      (∑ j,(supplyModel b V M p hV).rate N j*supplyMark .gross j) ≤ c*(V:ℝ))
    (s K : ℝ) (hs : 0 ≤ s) (N : BoxState V M) :
    supplyCycle .gross V M p hV (MarkedKernel.eventIndicator {a | K ≤ a.2}) N 0 ≤
      Real.exp (-s*K+4*c*(V:ℝ)*(Real.exp s-1)) := by
  have hstep (b : Bool) (X : BoxState V M) (z : ℝ) :
      (supplyKernel b .gross V M p hV).step (fun _ w => Real.exp (s*w)) X z ≤
      (1+(c/3000)*(Real.exp s-1))*Real.exp (s*z) := by
    let P := supplyKernel b .gross V M p hV
    have hm (j) : P.mark j=0 ∨ P.mark j=1 := by
      cases j with
      | none => exact Or.inl rfl
      | some j => exact supply_mark_binary .gross j
    apply bernoulli_mark_step P hm (c/3000) s hs
    intro Y
    simp only [P,supplyKernel,FiniteJumpModel.withMarks,Fintype.sum_option,mul_zero,zero_add,
      div_mul_eq_mul_div,← Finset.sum_div]
    apply (div_le_iff₀ (show 0 < 3000*(V:ℝ) by positivity)).mpr
    convert hcap b Y using 1
    ring
  have hp : 0 ≤ 1+c/3000*(Real.exp s-1) := by
    have he := Real.one_le_exp_iff.mpr hs
    positivity
  have h := three_stage_upper (supplyKernel false .gross V M p hV)
    (supplyKernel true .gross V M p hV) (supplyKernel true .gross V M p hV)
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) s
    (1+c/3000*(Real.exp s-1)) K hs hp (hstep false) (hstep true) (hstep true) N 0
  apply h.trans_eq
  congr 1
  norm_num only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat]
  ring

theorem pure_sharp_stopped_tail (V R : ℕ) (p : Parameters R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : p.capacity=R) (hd : p.cleavage=1/50)
    (hlarge : 1000000 ≤ V) (N : BoxState V R) :
    supplyCycle .gross V R p hV
      (MarkedKernel.eventIndicator {a | (V:ℝ)/10-1 ≤ a.2}) N 0 ≤ Real.exp (-(V:ℝ)/2000) := by
  have hh := supply_cycle_cap V R p hV (11/500) (by norm_num)
    (pure_supply_cap V R p hV hR hcapacity hd) (1/10) ((V:ℝ)/10-1) (by norm_num) N
  exact hh.trans (Real.exp_le_exp.mpr (sharp_rounded_exponent V (by exact_mod_cast hlarge)))

end
end FiniteReservoir

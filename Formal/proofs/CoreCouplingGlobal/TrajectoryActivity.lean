import proofs.CoreCouplingGlobal.GlobalConvergence
import proofs.CoreCouplingGlobal.EquilibriumBrackets
import proofs.CoreCouplingCAC.Activity

open Filter Topology Set
namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem stationary_activity_margins (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    (coreAB (flagshipRates e) s).2 ≤ -6 ∧
    4 ≤ (coreZH (flagshipRates e) s).1 ∧
    (1/2000:ℝ) ≤ (coreZH (flagshipRates e) s).2 := by
  obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,hbx,hby,hbw,hall⟩ :=
    exactly_three_bracketed_equilibria e hl hu
  have hcases := (hall s hs (by simpa only [flagship_eq_vary] using hss)).1
  have hz : (9/10:ℝ) ≤ s.z ∧ s.z ≤ 31/10 := by
    rcases hcases with rfl | rfl | rfl
    · constructor <;> linarith [hbx.1,hbx.2]
    · constructor <;> linarith [hby.1,hby.2]
    · exact ⟨by linarith [hbw.1],hbw.2⟩
  have hrec := stationary_reconstruction (flagshipRates e) s
    (by linarith : s.z+2 ≠ 0) (by norm_num [flagshipRates]) hss
  have hB : s.B = 60/(s.z+2) := by
    have h := congrArg State.B hrec
    norm_num [lift,reducedB,flagshipRates] at h ⊢
    exact h
  have hH := hss.2.2.2
  dsimp [fH,flagshipRates] at hH
  have hAB := (stationary_AB_margins (flagshipRates e) s hss).2
  have hzmargin := stationary_z_margin (flagshipRates e) s hss
    (by norm_num [flagshipRates])
  have hhmargin := stationary_H_margin (flagshipRates e) s hss
  have hb : s.B ≤ 21 := by
    rw [hB]
    apply (div_le_iff₀ (by linarith : 0 < s.z+2)).2
    linarith [hz.1]
  have hq : 0 ≤ (s.z-9/10)*(31/10-s.z) :=
    mul_nonneg (by linarith [hz.1]) (by linarith [hz.2])
  refine ⟨?_,?_,?_⟩
  · rw [hAB]
    change s.B-27 ≤ -6
    linarith
  · rw [hzmargin]
    norm_num [flagshipRates]
    nlinarith only [hq,hz.1,hz.2]
  · rw [hhmargin]
    change (1/2000:ℝ) ≤ (1/10000)*s.H
    nlinarith [sq_nonneg s.z,hz.1]

/-- Actual net-current margins converge by continuity of their polynomial formulas. -/
theorem trajectory_activity_limits (e : ℝ) (X : ℝ → State) (s : State)
    (hlim : Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))) :
    Tendsto (fun t => (coreAB (flagshipRates e) (X t)).2) atTop
      (𝓝 ((coreAB (flagshipRates e) s).2)) ∧
    Tendsto (fun t => (coreZH (flagshipRates e) (X t)).1) atTop
      (𝓝 ((coreZH (flagshipRates e) s).1)) ∧
    Tendsto (fun t => (coreZH (flagshipRates e) (X t)).2) atTop
      (𝓝 ((coreZH (flagshipRates e) s).2)) := by
  have hA := (tendsto_pi_nhds.1 hlim) 0
  have hB := (tendsto_pi_nhds.1 hlim) 1
  have hz := (tendsto_pi_nhds.1 hlim) 2
  have hH := (tendsto_pi_nhds.1 hlim) 3
  change Tendsto (fun t => (X t).A) atTop (𝓝 s.A) at hA
  change Tendsto (fun t => (X t).B) atTop (𝓝 s.B) at hB
  change Tendsto (fun t => (X t).z) atTop (𝓝 s.z) at hz
  change Tendsto (fun t => (X t).H) atTop (𝓝 s.H) at hH
  exact ⟨(hA.sub (hB.mul hz)).sub (tendsto_const_nhds.mul (hB.sub (hA.pow 2))),
    ((tendsto_const_nhds.mul hz).sub hH).neg.add
      (tendsto_const_nhds.mul (hH.sub (tendsto_const_nhds.mul (hz.pow 2)))),
    ((tendsto_const_nhds.mul hz).sub hH).sub
      (hH.sub (tendsto_const_nhds.mul (hz.pow 2)))⟩

/-- Every positive trajectory eventually has the same strict activity signs,
with explicit margins independent of the selected equilibrium and parameter. -/
theorem every_trajectory_eventual_activity (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    ∀ᶠ t in atTop, (coreAB (flagshipRates e) (X t)).2 < -3 ∧
      2 < (coreZH (flagshipRates e) (X t)).1 ∧
      (1/4000:ℝ) < (coreZH (flagshipRates e) (X t)).2 := by
  obtain ⟨s,hs,hss,hlim⟩ := trajectory_converges_to_positive_equilibrium e hl hu X hX
  obtain ⟨hb,hz,hh⟩ := stationary_activity_margins e hl hu s hs hss
  obtain ⟨lb,lz,lh⟩ := trajectory_activity_limits e X s hlim
  filter_upwards [lb.eventually (gt_mem_nhds (by linarith :
      (coreAB (flagshipRates e) s).2 < -3)),
    lz.eventually (lt_mem_nhds (by linarith : 2 < (coreZH (flagshipRates e) s).1)),
    lh.eventually (lt_mem_nhds (by linarith :
      (1/4000:ℝ) < (coreZH (flagshipRates e) s).2))] with t ht hz hh
  exact ⟨ht,hz,hh⟩

/-- Sustained simultaneous productivity consumes a bounded concentration range. -/
theorem simultaneous_productivity_duration (e η a b : ℝ) (hη : 0 < η)
    (ha : 0 ≤ a) (hab : a ≤ b) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) (hzb : (X b).z ≤ 12)
    (hprod : ∀ t ∈ Icc a b, η ≤ (coreAB (flagshipRates e) (X t)).1 ∧
      η ≤ (coreAB (flagshipRates e) (X t)).2 ∧
      η ≤ (coreZH (flagshipRates e) (X t)).1) : b-a ≤ 3/η := by
  let g : ℝ → ℝ := fun t => (X t).z-4*η*t
  let g' : ℝ → ℝ := fun t =>
    fZ (flagshipRates e) (X t).A (X t).B (X t).z (X t).H-4*η
  have hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t := by
    intro t ht
    simpa [g,g'] using
      (hX.dz t (ha.trans ht.1)).sub ((hasDerivAt_id t).const_mul (4*η))
  have hm : MonotoneOn g (Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      obtain ⟨h₁,h₂,h₃⟩ := hprod t (interior_subset ht)
      have hg := uniform_productivity_z_growth (flagshipRates e) (X t) η h₁ h₂ h₃
      dsimp [g']
      linarith
  have hdiff := hm (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  have hza := (hX.positive a ha).2.2.1
  dsimp [g] at hdiff
  apply (le_div_iff₀ hη).2
  nlinarith

/-- Restrict stoichiometric rows and columns, but evaluate currents at the
same full physical state and rate vector. -/
noncomputable def literalCoreProduction (p : Rates) (x : State)
    (species : Fin 2 → Fin 4) (reactions : Fin 2 → Fin 7) (i : Fin 2) : ℝ :=
  ∑ r : Fin 2, ((outputComplex (species i) (reactions r) : ℝ) -
    inputComplex (species i) (reactions r))*sourceCurrent p x (reactions r)

private theorem vec_seven_fifth {α : Type*} (a b c d e f g : α) :
    (![a,b,c,d,e,f,g] : Fin 7 → α) 5 = f := rfl

theorem actual_core_production_adapter (p : Rates) (x : State) :
    literalCoreProduction p x abSpecies abReactions = ![(coreAB p x).1,(coreAB p x).2] ∧
    literalCoreProduction p x zhSpecies zhReactions = ![(coreZH p x).1,(coreZH p x).2] := by
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [literalCoreProduction,sourceCurrent,inputComplex,outputComplex,
      forwardRate,reverseRate,coordinates,abSpecies,abReactions,zhSpecies,zhReactions,
      Fin.sum_univ_succ,Fin.prod_univ_succ,coreAB,coreZH,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,vec_seven_fifth] <;> ring

/-- Positive production in this gain-two core forces both net orientations. -/
theorem productive_currents_positive (j k : ℝ) (h : CoreProductive j k) :
    0 < j ∧ 0 < k := by
  obtain ⟨h₁,h₂⟩ := h
  constructor <;> linarith

theorem actual_current_productivity_iff (p : Rates) (x : State) :
    (CoreProductive (sourceCurrent p x 0) (sourceCurrent p x 5) ↔
      0 < (coreAB p x).1 ∧ 0 < (coreAB p x).2) ∧
    (CoreProductive (sourceCurrent p x 1) (sourceCurrent p x 2) ↔
      0 < (coreZH p x).1 ∧ 0 < (coreZH p x).2) := by
  constructor <;> norm_num [sourceCurrent,inputComplex,outputComplex,forwardRate,reverseRate,
    coordinates,Fin.prod_univ_succ,CoreProductive,coreAB,coreZH,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.vecHead,Matrix.vecTail,vec_seven_fifth]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1,h.2]

/-- Actual-current strict activity, including net reaction orientations. -/
theorem eventual_actual_core_signature (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    ∀ᶠ t in atTop,
      ¬ CoreProductive (sourceCurrent (flagshipRates e) (X t) 0)
        (sourceCurrent (flagshipRates e) (X t) 5) ∧
      CoreProductive (sourceCurrent (flagshipRates e) (X t) 1)
        (sourceCurrent (flagshipRates e) (X t) 2) ∧
      0 < sourceCurrent (flagshipRates e) (X t) 1 ∧
      0 < sourceCurrent (flagshipRates e) (X t) 2 := by
  filter_upwards [every_trajectory_eventual_activity e hl hu X hX] with t ht
  obtain ⟨hab,hzh⟩ := actual_current_productivity_iff (flagshipRates e) (X t)
  have hp := hzh.2 ⟨by linarith [ht.2.1],by linarith [ht.2.2]⟩
  exact ⟨fun h => by have hh := (hab.1 h).2; linarith [ht.1],hp,
    productive_currents_positive _ _ hp⟩

end CoreCouplingGlobal

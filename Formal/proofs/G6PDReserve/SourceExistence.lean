import proofs.G6PDReserve.RecoveryClassification
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

namespace G6PDReserve
noncomputable section
open Set Metric

/-- A bounded globally Lipschitz autonomous field has a solution on every
requested finite horizon, with genuine derivatives even at the endpoints. -/
theorem bounded_lipschitz_solution (f : ℝ → ℝ) (K L : NNReal)
    (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)
    (x T : ℝ) (hT : 0 ≤ T) :
    ∃ g : ℝ → ℝ, g 0 = x ∧ ∀ t ∈ Icc 0 T, HasDerivAt g (f (g t)) t := by
  let a : NNReal := L * ⟨T+1,by linarith⟩
  have hf : IsPicardLindelof (fun _ => f)
      (tmin := -1) (tmax := T+1) ⟨0,by constructor <;> linarith⟩ x a 0 L K := by
    constructor
    · intro t ht
      exact hK.lipschitzOnWith
    · intro y hy
      exact continuousOn_const
    · intro t ht y hy
      exact hL y
    · simp only [sub_zero, zero_sub, neg_neg, NNReal.coe_zero, NNReal.coe_mul, a]
      rw [max_eq_left (by linarith : (1:ℝ) ≤ T+1)]
      exact le_rfl
  obtain ⟨g,h0,hd⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨g,h0,?_⟩
  intro t ht
  exact (hd t ⟨by linarith [ht.1],by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

/-- Compact-interval inward fields: clipping is an existence device only.
The returned trajectory solves the original, unclipped equation. -/
theorem compact_inward_solution (f : ℝ → ℝ) (P x T : ℝ)
    (hP : 0 < P) (hx : x ∈ Icc 0 P) (hT : 0 ≤ T)
    (hf : ContDiffOn ℝ 1 f (Icc 0 P)) (hleft : 0 ≤ f 0) (hright : f P < 0) :
    ∃ g : ℝ → ℝ, g 0 = x ∧
      (∀ t ∈ Icc 0 T, g t ∈ Icc 0 P) ∧
      ∀ t ∈ Icc 0 T, HasDerivAt g (f (g t)) t := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  let F : ℝ → ℝ := fun z => f (projIcc 0 P hP.le z)
  have hFK : LipschitzWith K F := by
    simpa [F] using hK.to_restrict.comp (LipschitzWith.projIcc hP.le)
  have hFC : ∀ z, ‖F z‖ ≤ (Real.toNNReal C : ℝ) := by
    intro z
    exact le_trans (hC _ (projIcc 0 P hP.le z).property) (Real.le_coe_toNNReal C)
  obtain ⟨g,h0,hd⟩ := bounded_lipschitz_solution F K (Real.toNNReal C) hFK hFC x T hT
  have hc : ContinuousOn g (Icc 0 T) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hupper : ∀ t ∈ Icc 0 T, g t ≤ P := by
    apply image_le_of_deriv_right_lt_deriv_boundary hc
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (show g 0 ≤ (fun _ : ℝ => P) 0 by rw [h0]; exact hx.2)
      (fun t => hasDerivAt_const t P)
    intro t ht he
    change F (g t) < 0
    rw [he]
    simpa [F,projIcc_of_mem _ (show P ∈ Icc 0 P from ⟨hP.le,le_rfl⟩)] using hright
  have hlower : ∀ t ∈ Icc 0 T, 0 ≤ g t := by
    intro u hu
    by_contra hn
    have hneg : g u < 0 := lt_of_not_ge hn
    let ε := -g u/(2*(T+1))
    have hε : 0 < ε := div_pos (neg_pos.mpr hneg) (by positivity)
    have hB (t : ℝ) : HasDerivAt (fun t => ε*(t+1)) ε t := by
      simpa using ((hasDerivAt_id t).add_const 1).const_mul ε
    have hh := image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).neg.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).neg.hasDerivWithinAt)
      (show -g 0 ≤ (fun t => ε*(t+1)) 0 by rw [h0]; dsimp; nlinarith [hx.1])
      hB (by
        intro t ht he
        have hgt : g t ≤ 0 := by dsimp at he; nlinarith [ht.1]
        change -F (g t) < ε
        have heF : F (g t) = f 0 := by simp [F,projIcc_of_le_left _ hgt]
        rw [heF]
        linarith) hu
    have he : ε*(2*(T+1)) = -g u := by dsimp [ε]; field_simp
    have hh2 : ε*(u+1) ≤ ε*(T+1) := mul_le_mul_of_nonneg_left (by linarith [hu.2]) hε.le
    dsimp at hh
    nlinarith
  refine ⟨g,h0,fun t ht => ⟨hlower t ht,hupper t ht⟩,?_⟩
  intro t ht
  have heF : F (g t) = f (g t) := by
    simp [F,projIcc_of_mem _ (show g t ∈ Icc 0 P from ⟨hlower t ht,hupper t ht⟩)]
  simpa only [heF] using hd t ht

theorem scalar_solution_exists (a b c P q x T : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hP : 0 < P) (hq : 0 < q)
    (hx : x ∈ Icc 0 P) (hT : 0 ≤ T) (hboundary : q ≤ scalarRate a b c P 0) :
    ∃ g : ℝ → ℝ, g 0 = x ∧ (∀ t ∈ Icc 0 T, g t ∈ Icc 0 P) ∧
      ∀ t ∈ Icc 0 T, HasDerivAt g (scalarRate a b c P (g t)-q) t := by
  apply compact_inward_solution (fun z => scalarRate a b c P z-q) P x T hP hx hT
  · unfold scalarRate
    apply ContDiffOn.sub _ contDiffOn_const
    apply ContDiffOn.div
    · fun_prop
    · fun_prop
    · intro z hz
      exact ne_of_gt (scalar_den_pos a b c P z ha hb hc hz.1 hz.2)
  · linarith
  · simpa [scalarRate] using neg_neg_of_pos hq

theorem compact_solution_unique (f g h : ℝ → ℝ) (P T : ℝ)
    (hf : ContDiffOn ℝ 1 f (Icc 0 P))
    (hg : ∀ t ∈ Icc 0 T, g t ∈ Icc 0 P)
    (hh : ∀ t ∈ Icc 0 T, h t ∈ Icc 0 P)
    (hdg : ∀ t ∈ Icc 0 T, HasDerivAt g (f (g t)) t)
    (hdh : ∀ t ∈ Icc 0 T, HasDerivAt h (f (h t)) t)
    (h0 : g 0 = h 0) : EqOn g h (Icc 0 T) := by
  obtain ⟨K,hK⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => f) (s := fun _ => Icc 0 P)
    (fun _ _ => hK) (fun t ht => (hdg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hg t (Ico_subset_Icc_self ht))
    (fun t ht => (hdh t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdh t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hh t (Ico_subset_Icc_self ht)) h0

/-- Existence-based classification, not conditional on a supplied trajectory. -/
theorem scalar_recovery_iff (a b c P q x R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hP : 0 < P) (hq : 0 < q)
    (hx : 0 ≤ x) (hxR : x < R) (hRP : R < P)
    (hboundary : q ≤ scalarRate a b c P 0) :
    (∃ T > (0:ℝ), ∃ g : ℝ → ℝ, g 0 = x ∧
      (∀ t ∈ Icc 0 T, g t ∈ Icc 0 P) ∧
      (∀ t ∈ Icc 0 T, HasDerivAt g (scalarRate a b c P (g t)-q) t) ∧ R ≤ g T) ↔
      q < scalarRate a b c P R := by
  have hRR : R ∈ Icc 0 P := ⟨by linarith,hRP.le⟩
  have hxx : x ∈ Icc 0 P := ⟨hx,by linarith⟩
  have hanti := scalar_rate_strictAnti a b c P ha hb hc hP
  constructor
  · rintro ⟨T,hT,g,h0,hpool,hd,hend⟩
    by_contra hn
    have hh := decreasing_rate_no_finite_arrival (scalarRate a b c P) g P R q
      ((b*P+c)/c^2) T hT.le hRR (by rw [h0]; exact hxR) hpool hd hanti
      (le_of_not_gt hn) (fun z hz => scalar_secant_bound a b c P R z ha hb hc hP hRR hz)
    linarith
  · intro hmargin
    let m := scalarRate a b c P R-q
    have hm : 0 < m := sub_pos.mpr hmargin
    let T := (R-x)/m
    have hT : 0 < T := div_pos (sub_pos.mpr hxR) hm
    obtain ⟨g,h0,hpool,hd⟩ := scalar_solution_exists a b c P q x T ha hb hc hP hq hxx hT.le hboundary
    have htime : (R-g 0)/m = T := by rw [h0]
    obtain ⟨t,ht,hhit⟩ := positive_drift_reaches g R m hm (by rw [h0]; exact hxR)
      (by
        rw [htime]
        intro t ht
        simpa only [(hd t ht).deriv] using hd t ht)
      (by
        rw [htime]
        intro t ht hbelow
        rw [(hd t ht).deriv]
        have := hanti.antitoneOn (hpool t ht) hRR hbelow.le
        dsimp [m]
        linarith)
    rw [htime] at ht
    have htpos : 0 < t := by
      by_contra hn
      have he : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
      rw [he,h0] at hhit
      linarith
    exact ⟨t,htpos,g,h0,
      fun s hs => hpool s ⟨hs.1,le_trans hs.2 ht.2⟩,
      fun s hs => hd s ⟨hs.1,le_trans hs.2 ht.2⟩,hhit⟩

end
end G6PDReserve

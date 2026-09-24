import proofs.OverlappingSiphonInvasion.NormalizedMassDynamics

noncomputable section
open Set Filter Topology
namespace OverlappingSiphonInvasion

theorem accumulated_growth_positive_time (A G : ℝ → ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivAt A (G t) t)
    (hg : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t in atTop, δ < G t) :
    ∃ n : ℕ, 1 < A (n+1) := by
  obtain ⟨δ,hδ,hg⟩ := hg
  obtain ⟨T,hT⟩ := eventually_atTop.1 (hg.and (eventually_ge_atTop (0:ℝ)))
  have hT0 := (hT T le_rfl).2
  have hdq : ∀ t, T ≤ t → HasDerivAt (fun s => A s-δ*s) (G t-δ) t := by
    intro t ht
    simpa using (hd t (hT0.trans ht)).sub ((hasDerivAt_id t).const_mul δ)
  have hm : MonotoneOn (fun t => A t-δ*t) (Ici T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici T)
      (fun t ht => (hdq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdq t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => sub_nonneg.mpr (hT t (interior_subset ht)).1.le)
  obtain ⟨n,hn⟩ := exists_nat_gt (max T ((1-A T)/δ+T))
  have hnT : T ≤ (n:ℝ)+1 := by have hh := (le_max_left _ _).trans_lt hn; linarith
  have hng : (1-A T)/δ < (n:ℝ)+1-T := by
    have hh := (le_max_right _ _).trans_lt hn
    linarith
  have hb := hm (show T ∈ Ici T by simp) hnT hnT
  have hc := (div_lt_iff₀ hδ).mp hng
  refine ⟨n,?_⟩
  simpa only [Nat.cast_add,Nat.cast_one] using (show 1 < A ((n:ℝ)+1) by nlinarith only [hb,hc])

/-- The accumulated coordinate is the exact logarithmic multiplier even when
the product is zero. No division by the extinction product is used. -/
theorem exponential_growth_identity (P A G : ℝ → ℝ)
    (hP : ∀ t, 0 ≤ t → HasDerivAt P (G t*P t) t)
    (hA : ∀ t, 0 ≤ t → HasDerivAt A (G t) t) (hA0 : A 0 = 0) :
    ∀ t, 0 ≤ t → P t = Real.exp (A t)*P 0 := by
  let Q : ℝ → ℝ := fun t => Real.exp (-A t)*P t
  have hdQ : ∀ t, 0 ≤ t → HasDerivAt Q 0 t := by
    intro t ht
    convert ((hA t ht).neg.exp).mul (hP t ht) using 1
    ring
  have hu := CoreCouplingGlobal.scalar_upper_barrier Q (fun _ => 0) (Q 0) hdQ le_rfl
    (fun _ _ _ => le_rfl)
  have hl := CoreCouplingGlobal.scalar_lower_barrier Q (fun _ => 0) (Q 0) hdQ le_rfl
    (fun _ _ _ => le_rfl)
  intro t ht
  have hh := le_antisymm (hu t ht) (hl t ht)
  have hh' := congrArg (fun v => Real.exp (A t)*v) hh
  dsimp [Q] at hh'
  simpa only [hA0,neg_zero,Real.exp_zero,one_mul,← mul_assoc,← Real.exp_add,
    add_neg_cancel] using hh'

end OverlappingSiphonInvasion

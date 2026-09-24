import proofs.CoreCouplingGlobal.FirstExit

namespace CoreCouplingGlobal
open Set

/-- A fixed positive dissipation cost prevents escape when the initial energy
budget above a lower bound is too small. The last short interval before first
exit replaces a separate last-inner-hit construction. -/
theorem annular_energy_prevents_exit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (q : E → ℝ)
    (X : ℝ → E) (V : ℝ → ℝ) (p : E)
    (r M d L : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t)
    (hspeed : ∀ x, dist x p ≤ r → ‖f x‖ ≤ M)
    (hcost : ∀ x, r/2 ≤ dist x p → dist x p ≤ r → d ≤ q x)
    (henergy : ∀ t, 0 ≤ t → ∃ v, HasDerivAt V v t ∧ v ≤ -q (X t))
    (hanti : AntitoneOn V (Ici 0)) (hlower : ∀ t, 0 ≤ t → L ≤ V t)
    (hinit : dist (X 0) p < r/2) (hbudget : V 0 < L+d*(r/(2*M))) :
    ∀ t, 0 ≤ t → dist (X t) p < r := by
  intro T hT
  by_contra hbad
  have hc : ContinuousOn (fun t => dist (X t) p) (Icc 0 T) := by
    have hcx : ContinuousOn X (Icc 0 T) :=
      fun t ht => (hX t ht.1).continuousAt.continuousWithinAt
    simpa only [dist_eq_norm] using (hcx.sub (continuousOn_const (c := p))).norm
  obtain ⟨τ,hτ,hlevel,hbefore⟩ := first_level_hit _ T r hT hc (by linarith) (le_of_not_gt hbad)
  have hinside : ∀ t ∈ Icc 0 τ, dist (X t) p ≤ r := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hbefore t ⟨ht.1,hlt⟩).le
    · exact hlevel.le
  have htravel : ∀ u ∈ Icc 0 τ, ∀ v ∈ Icc u τ, dist (X v) (X u) ≤ M*(v-u) := by
    intro u hu v hv
    rw [dist_eq_norm]
    exact norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (hX t (hu.1.trans ht.1)).hasDerivWithinAt)
      (fun t ht => hspeed (X t) (hinside t ⟨hu.1.trans ht.1,ht.2.le⟩)) v hv
  let h := r/(2*M)
  have hh : 0 < h := by dsimp [h]; positivity
  have hMh : M*h=r/2 := by dsimp [h]; field_simp
  have hτlong : h < τ := by
    have hdist := dist_triangle (X τ) (X 0) p
    have hstep := htravel 0 ⟨le_rfl,hτ.1.le⟩ τ ⟨hτ.1.le,le_rfl⟩
    rw [hlevel] at hdist
    simp only [sub_zero] at hstep
    have hprod : M*h < M*τ := by linarith
    nlinarith
  let a := τ-h
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have haτ : a < τ := by dsimp [a]; linarith
  have hannulus : ∀ t ∈ Icc a τ, r/2 ≤ dist (X t) p := by
    intro t ht
    have ht0 := ha.trans ht.1
    have hstep := htravel t ⟨ht0,ht.2⟩ τ ⟨ht.2,le_rfl⟩
    have htri := dist_triangle (X τ) (X t) p
    rw [hlevel] at htri
    have hdt : τ-t ≤ h := by dsimp [a] at ht; linarith [ht.1]
    have hprod := mul_le_mul_of_nonneg_left hdt hM.le
    linarith
  let W := fun t => V t+d*t
  have hWd : ∀ t ∈ Icc a τ, ∃ v, HasDerivAt W v t ∧ v ≤ 0 := by
    intro t ht
    obtain ⟨v,hv,hvbound⟩ := henergy t (ha.trans ht.1)
    have hqd := hcost (X t) (hannulus t ht) (hinside t ⟨ha.trans ht.1,ht.2⟩)
    refine ⟨v+d,?_,by linarith⟩
    have hdt : HasDerivAt (fun u : ℝ => d*u) d t := by
      simpa only [mul_one] using (hasDerivAt_id t).const_mul d
    exact hv.add hdt
  have hWanti : AntitoneOn W (Icc a τ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a τ)
    · intro t ht
      exact (hWd t ht).choose_spec.1.continuousAt.continuousWithinAt
    · intro t ht
      exact (hWd t (interior_subset ht)).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨v,hv,hv0⟩ := hWd t (interior_subset ht)
      rw [hv.deriv]
      exact hv0
  have hdrop := hWanti ⟨le_rfl,haτ.le⟩ ⟨haτ.le,le_rfl⟩ haτ.le
  have hstart := hanti (show (0:ℝ) ∈ Ici 0 by simp) ha ha
  have hlow := hlower τ hτ.1.le
  change V 0 < L+d*h at hbudget
  dsimp [W,a] at hdrop
  nlinarith

end CoreCouplingGlobal

import proofs.OverlappingSiphonInvasion.GeneralFlow

noncomputable section
namespace OverlappingSiphonInvasion

theorem bounded_source_unique (p : Rates) (R : ℝ) (X Y : ℝ → State)
    (hXd : ∀ t, 0 ≤ t → HasDerivAt X (field p (X t)) t)
    (hYd : ∀ t, 0 ≤ t → HasDerivAt Y (field p (Y t)) t)
    (hX : ∀ t, 0 ≤ t → X t ∈ populationBox R)
    (hY : ∀ t, 0 ≤ t → Y t ∈ populationBox R) (h0 : X 0 = Y 0) :
    ∀ t, 0 ≤ t → X t = Y t := by
  obtain ⟨K,hK⟩ := bounded_source_dependence p R
  intro t ht
  have hh := hK X Y hXd hYd hX hY t ht
  have hz : dist (X t) (Y t) ≤ 0 := by simpa only [h0,dist_self,zero_mul] using hh
  exact dist_le_zero.mp hz

def boxAdvance (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (t : ℝ) (ht : 0 ≤ t)
    (x : populationBox R) : populationBox R :=
  ⟨boxFlow p hp R x t,(boxFlow_spec p hp R hR x).2.1 t ht⟩

theorem boxAdvance_continuous (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (t : ℝ) (ht : 0 ≤ t) :
    Continuous (boxAdvance p hp R hR t ht) :=
  (boxFlow_continuous p hp R hR t ht).subtype_mk _

theorem boxFlow_add (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (x : populationBox R)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    boxFlow p hp R x (s+t) = boxFlow p hp R (boxAdvance p hp R hR s hs x) t := by
  let X : ℝ → State := fun τ => boxFlow p hp R x (s+τ)
  let y := boxAdvance p hp R hR s hs x
  have hx := boxFlow_spec p hp R hR x
  have hy := boxFlow_spec p hp R hR y
  have hXd : ∀ τ, 0 ≤ τ → HasDerivAt X (field p (X τ)) τ := by
    intro τ hτ
    simpa [X] using (hx.2.2 (s+τ) (add_nonneg hs hτ)).scomp τ
      ((hasDerivAt_id τ).const_add s)
  have hX : ∀ τ, 0 ≤ τ → X τ ∈ populationBox R :=
    fun τ hτ => hx.2.1 (s+τ) (add_nonneg hs hτ)
  have h0 : X 0 = boxFlow p hp R y 0 := by
    rw [hy.1]
    simp [X,y,boxAdvance]
  exact bounded_source_unique p R X (boxFlow p hp R y) hXd hy.2.2 hX hy.2.1 h0 t ht

/-- Any initially positive coordinate remains positive, even when other
coordinates start on a resident face. -/
theorem boxFlow_coordinate_positive (p : Rates) (hp : PositiveRates p) (R : ℝ)
    (hR : p.recruitment/deathFloor p+1 ≤ R) (x : populationBox R)
    (i : Fin 4) (hi : 0 < x.val i) (t : ℝ) (ht : 0 ≤ t) :
    0 < boxFlow p hp R x t i := by
  have hx := boxFlow_spec p hp R hR x
  have hu : ∀ s, 0 ≤ s → ∀ j, boxFlow p hp R x s j ≤ R := by
    intro s hs j
    have h0 := (hx.2.1 s hs).1 0
    have h1 := (hx.2.1 s hs).1 1
    have h2 := (hx.2.1 s hs).1 2
    have h3 := (hx.2.1 s hs).1 3
    have hN := (hx.2.1 s hs).2
    dsimp [total] at hN
    fin_cases j <;> dsimp <;> linarith
  apply CoreCouplingGlobal.positive_of_linear_lower
    (fun s => boxFlow p hp R x s i) (fun s => field p (boxFlow p hp R x s) i)
    (lossBound p R) (fun s hs => hasDerivAt_pi.1 (hx.2.2 s hs) i)
    (by simpa only [hx.1] using hi)
    (fun s hs => field_linear_lower p hp R _ (hx.2.1 s hs).1 (hu s hs) i) t ht

end OverlappingSiphonInvasion

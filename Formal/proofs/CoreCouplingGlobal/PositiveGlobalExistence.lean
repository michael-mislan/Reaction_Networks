import proofs.CoreCouplingGlobal.ExtensionBounds

namespace CoreCouplingGlobal
open CoreCouplingCAC

theorem positive_global_solution (e : ℝ) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (x₀ : State) (hx₀ : x₀.Positive) :
    ∃ X : ℝ → State, X 0 = x₀ ∧ IsPositiveTrajectory e X := by
  let S := max (x₀.A+x₀.B) 34
  let W := max (x₀.z+(7/4:ℝ)*x₀.H) ((7/2)*(S+76))
  let R := max S W+1
  have hS : 34 ≤ S := le_max_right _ _
  have hR : 1 ≤ R := by
    have hh : S ≤ max S W := le_max_left _ _
    dsimp [R]
    linarith
  obtain ⟨b,X,hb,hbone,hX0,hXd⟩ := positive_extension_solution e R (by linarith) (encodeState x₀)
  have hinit : ∀ i, 0 < X 0 i := by
    rw [hX0]
    intro i
    fin_cases i
    · exact hx₀.1
    · exact hx₀.2.1
    · exact hx₀.2.2.1
    · exact hx₀.2.2.2
  have hnonneg := extension_nonnegative e he b (fun x => (hb x).1) X (fun i => (hinit i).le) hXd
  have hpart : ∀ t, 0 ≤ t → positivePart (X t) = X t := by
    intro t ht
    funext i
    exact max_eq_right (hnonneg t ht i)
  have hscaled : ∀ t, 0 ≤ t → HasDerivAt X (b (X t) • responseVectorField e (X t)) t := by
    intro t ht
    simpa only [hpart t ht] using hXd t
  have hs := extension_total_bound e S he he' hS b (fun x => (hb x).1) X hnonneg
    (by simpa only [hX0,encodeState,Matrix.cons_val_zero,Matrix.cons_val_one] using (le_max_left (x₀.A+x₀.B) 34)) hscaled
  have hw := extension_weighted_bound e S W (le_max_right _ _) b (fun x => (hb x).1) X hnonneg hs
    (by simpa only [hX0,encodeState,Matrix.cons_val_two,Matrix.cons_val_three] using
      (le_max_left (x₀.z+(7/4:ℝ)*x₀.H) ((7/2)*(S+76)))) hscaled
  have hupper : ∀ t, 0 ≤ t → ∀ i, X t i ≤ R := by
    intro t ht i
    have h₀ := hnonneg t ht 0
    have h₁ := hnonneg t ht 1
    have h₂ := hnonneg t ht 2
    have h₃ := hnonneg t ht 3
    have hs' := hs t ht
    have hw' := hw t ht
    have hSR : S ≤ R := by dsimp [R]; linarith [le_max_left S W]
    have hWR : W ≤ R := by dsimp [R]; linarith [le_max_right S W]
    fin_cases i
    · change X t 0 ≤ R
      linarith
    · change X t 1 ≤ R
      linarith
    · change X t 2 ≤ R
      linarith
    · change X t 3 ≤ R
      linarith
  have hnorm : ∀ t, 0 ≤ t → ‖X t‖ ≤ R := by
    intro t ht
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R)).2
    intro i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hnonneg t ht i)] using hupper t ht i
  have hd : ∀ t, 0 ≤ t → HasDerivAt X (responseVectorField e (X t)) t := by
    intro t ht
    simpa only [hbone _ (hnorm t ht),one_smul] using hscaled t ht
  have hpos : ∀ t, 0 ≤ t → ∀ i, 0 < X t i := by
    intro t ht i
    exact positive_of_linear_lower (fun t => X t i) (fun t => responseVectorField e (X t) i)
      (20+6*R) (fun s hs => hasDerivAt_pi.1 (hd s hs) i) (hinit i)
      (fun s hs => response_linear_lower e R he he' hR (X s) (hnonneg s hs) (hupper s hs) i) t ht
  refine ⟨fun t => decodeState (X t),?_,?_⟩
  · change decodeState (X 0) = x₀
    rw [hX0,decode_encodeState]
  · constructor
    · intro t ht
      exact ⟨hpos t ht 0,hpos t ht 1,hpos t ht 2,hpos t ht 3⟩
    · intro t ht
      exact hasDerivAt_pi.1 (hd t ht) 0
    · intro t ht
      exact hasDerivAt_pi.1 (hd t ht) 1
    · intro t ht
      exact hasDerivAt_pi.1 (hd t ht) 2
    · intro t ht
      exact hasDerivAt_pi.1 (hd t ht) 3

end CoreCouplingGlobal

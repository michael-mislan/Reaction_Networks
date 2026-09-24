import proofs.DiagnosticWindows.Comparison

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

noncomputable def loadPolynomial (f : Fin 6 → ℝ) (l : ℝ) : ℝ :=
  f 0+l*f 1+l^2/2*f 2+l^3/6*f 3+l^4/24*f 4

theorem load_derivative (f : Fin 6 → ℝ) (l : ℝ) :
    HasDerivAt (fun x => Real.exp (-x)*loadPolynomial f x)
      (Real.exp (-l)*((f 1-f 0)+l*(f 2-f 1)+l^2/2*(f 3-f 2)+
        l^3/6*(f 4-f 3)-l^4/24*f 4)) l := by
  have h0 := (hasDerivAt_const l (f 0)).add ((hasDerivAt_id l).mul_const (f 1))
  have h1 := h0.add ((((hasDerivAt_id l).pow 2).div_const 2).mul_const (f 2))
  have h2 := h1.add ((((hasDerivAt_id l).pow 3).div_const 6).mul_const (f 3))
  have hp := h2.add ((((hasDerivAt_id l).pow 4).div_const 24).mul_const (f 4))
  convert (((hasDerivAt_id l).neg).exp).mul hp using 1
  simp [Pi.add_apply,Pi.pow_apply]
  ring

theorem loaded_antitone_poly (f : Fin 6 → ℝ) (hf : Antitone f) (hf4 : 0 ≤ f 4) :
    AntitoneOn (fun l : ℝ => Real.exp (-l)*loadPolynomial f l) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun l _ => (load_derivative f l).continuousAt.continuousWithinAt
  · exact fun l _ => (load_derivative f l).differentiableAt.differentiableWithinAt
  · intro l hl
    have hl0 : 0 ≤ l := interior_subset hl
    rw [(load_derivative f l).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have h0 : f 1-f 0 ≤ 0 := sub_nonpos.mpr (hf (by decide))
    have h1 : f 2-f 1 ≤ 0 := sub_nonpos.mpr (hf (by decide))
    have h2 : f 3-f 2 ≤ 0 := sub_nonpos.mpr (hf (by decide))
    have h3 : f 4-f 3 ≤ 0 := sub_nonpos.mpr (hf (by decide))
    have h4 : 0 ≤ l^4/24*f 4 := by positivity
    have h5 := mul_nonpos_of_nonneg_of_nonpos hl0 h1
    have h6 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ l^2/2) h2
    have h7 := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ l^3/6) h3
    linarith

theorem loading_polynomial (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (load t : NNReal) : loadedSurvival (birthKernel r hr) load t =
      Real.exp (-(load:ℝ))*loadPolynomial ((birthKernel r hr).poissonized t uncalled) load := by
  rw [loading_finite]
  norm_num [loadPolynomial,Finset.sum_range_succ,poissonWeight,loadIndex,Nat.factorial]
  simp only [show (⟨2,by decide⟩ : Fin 6) = 2 from rfl,
    show (⟨3,by decide⟩ : Fin 6) = 3 from rfl,
    show (⟨4,by decide⟩ : Fin 6) = 4 from rfl]
  ring

theorem loading_antitone (r : Fin 6 → ℝ) (hr : ∀ z, r z ∈ Set.Icc 0 1)
    (t : NNReal) : Antitone (fun load => loadedSurvival (birthKernel r hr) load t) := by
  intro a b hab
  change loadedSurvival (birthKernel r hr) b t ≤ loadedSurvival (birthKernel r hr) a t
  rw [loading_polynomial,loading_polynomial]
  apply loaded_antitone_poly _ (birth_survival_antitone_state r hr t) _ a.property b.property hab
  rw [uncalled_indicator]
  exact ((birthKernel r hr).poissonized_event_bounds _ _ _).1

theorem loaded_rate_order (r s : Fin 6 → ℝ)
    (hr : ∀ z, r z ∈ Set.Icc 0 1) (hs : ∀ z, s z ∈ Set.Icc 0 1)
    (hrs : ∀ z, r z ≤ s z) (load t : NNReal) :
    loadedSurvival (birthKernel s hs) load t ≤ loadedSurvival (birthKernel r hr) load t := by
  apply Summable.tsum_le_tsum
  · intro n
    exact mul_le_mul_of_nonneg_left (birth_survival_order r s hr hs hrs t (loadIndex n))
      (poissonWeight_nonneg load n)
  · exact loading_summable _ _ _
  · exact loading_summable _ _ _

end DiagnosticWindows

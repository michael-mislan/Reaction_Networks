import proofs.CoreCouplingGlobal.JacobianBinding

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Polynomial

theorem complex_spectrum_of_real_factorization (M : Matrix (Fin 4) (Fin 4) ℝ)
    (a b c d : ℝ) (h : M.charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d)) (ξ : ℂ) :
    ξ ∈ spectrum ℂ (M.map Complex.ofRealHom) ↔
      ξ = (a:ℂ) ∨ ξ = (b:ℂ) ∨ ξ = (c:ℂ) ∨ ξ = (d:ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,Matrix.charpoly_map,h]
  simp [Polynomial.IsRoot,mul_eq_zero,or_assoc,sub_eq_zero]

/-- The literal middle equilibrium has precisely four distinct real spectral
values: three negative and one positive, all in the displayed disjoint intervals. -/
theorem middle_physical_spectrum (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (0:ℝ) (1/10) ∧
      ∀ ξ : ℂ, ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom) ↔
        ξ = (a:ℂ) ∨ ξ = (b:ℂ) ∨ ξ = (c:ℂ) ∨ ξ = (d:ℂ) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hfactor⟩ := middle_physical_characteristic_factorization e he hu s hs hss hz
  exact ⟨a,b,c,d,ha,hb,hc,hd,complex_spectrum_of_real_factorization _ a b c d hfactor⟩

/-- Every spectral value of either outer equilibrium is real and strictly negative. -/
theorem outer_physical_spectrum (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (9/10:ℝ) (11/10) ∨ s.z ∈ Icc (29/10:ℝ) (31/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (-(1/2):ℝ) 0 ∧
      ∀ ξ : ℂ, ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom) ↔
        ξ = (a:ℂ) ∨ ξ = (b:ℂ) ∨ ξ = (c:ℂ) ∨ ξ = (d:ℂ) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hfactor⟩ := outer_physical_characteristic_factorization e he hu s hs hss hz
  exact ⟨a,b,c,d,ha,hb,hc,hd,complex_spectrum_of_real_factorization _ a b c d hfactor⟩

theorem middle_physical_spectrum_no_imaginary_axis (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) (ξ : ℂ)
    (hξ : ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom)) :
    ξ.im = 0 ∧ ξ.re ≠ 0 := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hall⟩ := middle_physical_spectrum e he hu s hs hss hz
  rcases (hall ξ).1 hξ with rfl | rfl | rfl | rfl
  all_goals simp only [Complex.ofReal_im,Complex.ofReal_re,true_and]
  · linarith [ha.2]
  · linarith [hb.2]
  · linarith [hc.2]
  · exact hd.1.ne'

theorem outer_physical_spectrum_left_half_plane (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (9/10:ℝ) (11/10) ∨ s.z ∈ Icc (29/10:ℝ) (31/10)) (ξ : ℂ)
    (hξ : ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom)) :
    ξ.im = 0 ∧ ξ.re < 0 := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hall⟩ := outer_physical_spectrum e he hu s hs hss hz
  rcases (hall ξ).1 hξ with rfl | rfl | rfl | rfl
  all_goals simp only [Complex.ofReal_im,Complex.ofReal_re,true_and]
  · linarith [ha.2]
  · linarith [hb.2]
  · linarith [hc.2]
  · exact hd.2

end CoreCouplingGlobal

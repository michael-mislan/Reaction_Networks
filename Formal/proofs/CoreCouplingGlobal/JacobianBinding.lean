import proofs.CoreCouplingGlobal.RealSpectralRoots

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Polynomial

noncomputable def physicalJacobian (e : ℝ) (x : ResponseVector) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2-4*e*x 0,x 2+2*e,x 1,0;
    1+2*e*x 0,-1-x 2-e,-x 1,0;
    1,-x 2,-x 1-16-8*x 2,3;
    0,0,16+4*x 2,-(20001/10000)]

theorem physicalJacobian_hasFDerivAt (e : ℝ) (x : ResponseVector) :
    HasFDerivAt (responseVectorField e) (physicalJacobian e x).toLin'.toContinuousLinearMap x := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) x
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) x
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) x
  have h3 := hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) x
  have hA := (((h0.const_mul 2).const_sub 6).add (h2.mul h1)).add
    ((h1.sub (h0.pow 2)).const_mul (2*e))
  have hB := ((h0.const_add 27).sub ((h2.const_add 1).mul h1)).sub
    ((h1.sub (h0.pow 2)).const_mul e)
  have hz := (((h0.sub (h1.mul h2)).sub (h2.const_mul 16)).sub
    ((h2.pow 2).const_mul 4)).add (h3.const_mul 3)
  have hH := ((h2.const_mul 16).add ((h2.pow 2).const_mul 2)).sub
    (h3.const_mul (20001/10000))
  apply hasFDerivAt_pi'.2
  intro i
  fin_cases i
  · convert hA using 1
    ext v
    simp [physicalJacobian,dotProduct,Fin.sum_univ_succ]
    ring
  · convert hB using 1
    ext v
    simp [physicalJacobian,dotProduct,Fin.sum_univ_succ]
    ring
  · convert hz using 1
    · ext v
      norm_num [responseVectorField,fZ,flagshipRates]
    · ext v
      simp [physicalJacobian,dotProduct,Fin.sum_univ_succ]
      ring
  · convert hH using 1
    · ext v
      norm_num [responseVectorField,fH,flagshipRates]
    · ext v
      simp [physicalJacobian,dotProduct,Fin.sum_univ_succ]
      ring

theorem stationary_physicalJacobian (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    physicalJacobian e (encodeState s) = stationaryJacobian e (e*s.A) s.z := by
  have hB := (stationary_response_center e he hu s hs hss).1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [physicalJacobian,stationaryJacobian,encodeState,hB] <;> ring

theorem stationary_spectral_parameter_bounds (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (9/10:ℝ) (31/10)) : 0 ≤ e*s.A ∧ e*s.A ≤ 17/25000 := by
  have hB := (stationary_response_center e he hu s hs hss).1
  have hBB : s.B ∈ Icc (2:ℝ) 34 := by
    rw [hB]
    exact curve_B_bounds s.z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hr := (positive_stationary_barrier_identities e he hu s hs hss).1
  have hA : s.A = responseA e s.B := by
    dsimp [responseTotal] at hr
    linarith
  have hAu : s.A ≤ 34 := by
    rw [hA]
    exact (response_bounds e s.B he hu hBB.1 hBB.2).2.trans (by norm_num)
  refine ⟨mul_nonneg he hs.1.le,?_⟩
  have hh := mul_le_mul hu hAu hs.1.le (by norm_num : (0:ℝ) ≤ 1/50000)
  linarith

theorem middle_physical_characteristic_factorization (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (0:ℝ) (1/10) ∧
      (physicalJacobian e (encodeState s)).charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  obtain ⟨hp,hpu⟩ := stationary_spectral_parameter_bounds e he hu s hs hss
    ⟨by linarith [hz.1],by linarith [hz.2]⟩
  rw [stationary_physicalJacobian e he hu s hs hss]
  exact middle_four_real_spectral_roots e (e*s.A) s.z he hu hp hpu hz

theorem outer_physical_characteristic_factorization (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (9/10:ℝ) (11/10) ∨ s.z ∈ Icc (29/10:ℝ) (31/10)) :
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
      c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (-(1/2):ℝ) 0 ∧
      (physicalJacobian e (encodeState s)).charpoly = (X-C a)*(X-C b)*(X-C c)*(X-C d) := by
  have hw : s.z ∈ Icc (9/10:ℝ) (31/10) := by
    rcases hz with h | h <;> exact ⟨by linarith [h.1],by linarith [h.2]⟩
  obtain ⟨hp,hpu⟩ := stationary_spectral_parameter_bounds e he hu s hs hss hw
  rw [stationary_physicalJacobian e he hu s hs hss]
  exact outer_four_real_spectral_roots e (e*s.A) s.z he hu hp hpu hz

end CoreCouplingGlobal

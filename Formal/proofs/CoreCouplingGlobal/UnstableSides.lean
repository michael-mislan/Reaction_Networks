import proofs.CoreCouplingGlobal.UnstableOrientation

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology

theorem nonzero_derivative_orients_local_sides (f : ℝ → ℝ) (b : ℝ)
    (hb : b ≠ 0) (hd : HasDerivAt f b 0) :
    ∀ᶠ a in 𝓝 (0:ℝ), a ≠ 0 → 0 < (f a-f 0)*(a*b) := by
  have hc := hd.continuousAt_div
  have hp := (hc.mul continuousAt_const).eventually_const_lt
    (show 0 < Function.update (fun x => (f x-f 0)/(x-0)) 0 b 0*b by
      simpa using mul_self_pos.mpr hb)
  filter_upwards [hp] with a ha hane
  have hratio : 0 < (f a-f 0)/a*b := by
    simpa [Function.update_of_ne hane] using ha
  have hpos := mul_pos hratio (sq_pos_of_ne_zero hane)
  have heq : ((f a-f 0)/a*b)*a^2=(f a-f 0)*(a*b) := by
    field_simp
  rwa [heq] at hpos

theorem physical_unstable_chart_sides (e : ℝ) (he : 0 ≤ e)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) (φ : ℝ → ResponseVector)
    (hφ0 : φ 0=encodeState s)
    (hφ : HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0) :
    let b := C (unstableInclusion 1) 1
    b ≠ 0 ∧ ∀ᶠ a in 𝓝 (0:ℝ), a ≠ 0 → 0 < (φ a 1-s.B)*(a*b) := by
  have hb := unstable_physical_tangent_B_ne_zero e he s hs hss μ C hC
  have hd : HasDerivAt (fun a => φ a 1) (C (unstableInclusion 1) 1) 0 :=
    hasDerivAt_pi.mp hφ.hasDerivAt 1
  refine ⟨hb,?_⟩
  simpa only [hφ0,encodeState] using nonzero_derivative_orients_local_sides _ _ hb hd

end CoreCouplingGlobal

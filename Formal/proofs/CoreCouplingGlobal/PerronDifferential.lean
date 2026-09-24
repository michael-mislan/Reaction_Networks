import proofs.CoreCouplingGlobal.PerronHalfLine

namespace CoreCouplingGlobal
open Set MeasureTheory Filter
open scoped BoundedContinuousFunction

theorem integral_positive_translate (f : ℝ → ℝ) (t : ℝ) :
    (∫ s in Ioi (0:ℝ), f (s+t)) = ∫ s in Ioi t, f s := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).setIntegral_preimage_emb
    (Homeomorph.addRight t).isClosedEmbedding.measurableEmbedding f (Ioi t)
  have hs : (fun s : ℝ => s+t) ⁻¹' Ioi t = Ioi (0:ℝ) := by
    ext s
    simp
  simpa only [hs] using h

theorem exponential_future_tail (ν : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    exponentialAverage ν 1 f t =
      Real.exp (ν*t)*(∫ s in Ioi t, Real.exp ((-ν)*s)*f s) := by
  rw [← integral_positive_translate (fun s => Real.exp ((-ν)*s)*f s) t,
    ← integral_const_mul]
  unfold exponentialAverage
  apply integral_congr_ae
  filter_upwards [] with s
  have he : Real.exp (ν*t)*Real.exp ((-ν)*(s+t))=Real.exp ((-ν)*s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [one_mul]
  rw [← mul_assoc,he,add_comm s t]

theorem exponential_forcing_tail_integrable (ν : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) :
    IntegrableOn (fun s => Real.exp ((-ν)*s)*f s) (Ioi t) :=
  (integrableOn_exp_mul_Ioi (neg_neg_of_pos hν) t).mul_bdd
    f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)

theorem continuous_tail_hasDerivAt (F : ℝ → ℝ) (hF : Continuous F)
    (hi : ∀ t, IntegrableOn F (Ioi t)) (t : ℝ) :
    HasDerivAt (fun u => ∫ s in Ioi u, F s) (-F t) t := by
  have hd := intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 t)
    hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have heq : (fun u => ∫ s in Ioi u, F s) =
      (fun u => (∫ s in Ioi (0:ℝ), F s)-(∫ s in (0:ℝ)..u, F s)) := by
    ext u
    have h := intervalIntegral.integral_Ioi_sub_Ioi' (hi 0) (hi u)
    linarith only [h]
  rw [heq]
  simpa using hd.const_sub (∫ s in Ioi (0:ℝ), F s)

/-- Future integration solves y'=nu*y-f for continuous bounded forcing. No
derivative of the forcing is assumed. -/
theorem exponential_future_hasDerivAt (ν : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) :
    HasDerivAt (exponentialAverage ν 1 f) (ν*exponentialAverage ν 1 f t-f t) t := by
  have hcont : Continuous (fun s : ℝ => Real.exp ((-ν)*s)*f s) :=
    (Real.continuous_exp.comp (by fun_prop)).mul f.continuous
  have ht := continuous_tail_hasDerivAt _ hcont (exponential_forcing_tail_integrable ν hν f) t
  have he := (((hasDerivAt_id t).const_mul ν).exp).mul ht
  have hprod : Real.exp (ν*t)*Real.exp ((-ν)*t)=1 := by
    rw [← Real.exp_add]
    simp
  have heq : exponentialAverage ν 1 f =
      (fun u => Real.exp (ν*u)*(∫ s in Ioi u, Real.exp ((-ν)*s)*f s)) := by
    funext u
    exact exponential_future_tail ν f u
  rw [heq]
  convert he using 1
  dsimp only [id_eq]
  linear_combination (f t)*hprod

noncomputable def reflectedForcing (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun t => -t,continuous_neg⟩

theorem exponential_past_reflection (ν : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) :
    exponentialAverage ν (-1) f t=exponentialAverage ν 1 (reflectedForcing f) (-t) := by
  unfold exponentialAverage
  apply integral_congr_ae
  filter_upwards [] with s
  change Real.exp ((-ν)*s)*f (t+(-1)*s) =
    Real.exp ((-ν)*s)*f (-(-t+1*s))
  rw [show t+(-1)*s = -(-t+1*s) by ring]

theorem exponential_past_hasDerivAt (ν : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) :
    HasDerivAt (exponentialAverage ν (-1) f) (-ν*exponentialAverage ν (-1) f t+f t) t := by
  have h := (exponential_future_hasDerivAt ν hν (reflectedForcing f) (-t)).comp t
    (hasDerivAt_neg t)
  have heq : exponentialAverage ν (-1) f =
      (fun u => exponentialAverage ν 1 (reflectedForcing f) (-u)) := by
    funext u
    exact exponential_past_reflection ν f u
  rw [heq]
  convert h using 1
  simp [reflectedForcing]
  ring

/-- The unclamped representative permits an ordinary two-sided derivative at
time zero. It agrees with the bounded corrected trajectory for t>=0. -/
noncomputable def uncutPastTrajectory (ν : ℝ) (f : ℝ →ᵇ ℝ) (t : ℝ) : ℝ :=
  exponentialAverage ν (-1) f t-Real.exp (-ν*t)*exponentialAverage ν (-1) f 0

theorem uncutPastTrajectory_agrees (ν : ℝ) (hν : 0 < ν) (f : ℝ →ᵇ ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    uncutPastTrajectory ν f t=pastZeroTrajectory ν hν f t := by
  simp [uncutPastTrajectory,pastZeroTrajectory,nonnegativeTime,decayingProfile,
    exponentialGreenOperator,exponentialAverageBCF,max_eq_left ht]
  ring

theorem uncutPastTrajectory_hasDerivAt (ν : ℝ) (hν : 0 < ν)
    (f : ℝ →ᵇ ℝ) (t : ℝ) :
    HasDerivAt (uncutPastTrajectory ν f) (-ν*uncutPastTrajectory ν f t+f t) t := by
  have h := (exponential_past_hasDerivAt ν hν f t).sub
    ((((hasDerivAt_id t).const_mul (-ν)).exp).mul_const (exponentialAverage ν (-1) f 0))
  convert h using 1
  dsimp [uncutPastTrajectory]
  ring

end CoreCouplingGlobal

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.Jacobian
import proofs.Bressan.Basic.Torus

/-!
# Periodic Euclidean ODE flows and descent to the torus

This file begins the producer from a genuine time-dependent Euclidean ODE.
The first lemma is the uniqueness step needed to descend a periodic lifted
velocity to the quotient: translating the initial point by a period translates
the complete trajectory by the same period.
-/

open MeasureTheory

namespace Bressan

/-- A globally bounded, globally spatially Lipschitz nonautonomous vector
field has simultaneous solutions for every initial point on a prescribed
compact time interval.  One global Picard ball of radius `M*T` suffices, so
no noncanonical finite chaining data enters the result. -/
theorem exists_odeTrajectoryOn_Icc_of_global_bounded_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : ℝ → E → E) (T K M : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (htime : ∀ x, ContinuousOn (fun t => v t x) (Set.Icc (0 : ℝ) T))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ M) :
    ∃ X : E → ℝ → E, ∀ x,
      X x 0 = x ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (X x) (v t (X x t)) (Set.Icc (0 : ℝ) T) t := by
  let t0 : Set.Icc (0 : ℝ) T := ⟨0, by simp⟩
  have hPL (x : E) : IsPicardLindelof
      (tmin := (0 : ℝ)) (tmax := (T : ℝ)) v t0 x (M * T) 0 M K := by
    refine {
      lipschitzOnWith := fun t _ht => (hv t).lipschitzOnWith
      continuousOn := fun y _hy => htime y
      norm_le := fun t ht y _hy => hbound t ht y
      mul_max_le := ?_ }
    ·
      change (M : ℝ) * max ((T : ℝ) - 0) (0 - 0) ≤
        (M * T : NNReal) - 0
      simp
  have hex (x : E) := (hPL x).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose X hX using hex
  refine ⟨X, ?_⟩
  intro x
  exact ⟨(hX x).1, (hX x).2⟩

/-- The same global Picard ball constructs trajectories from every starting
time in the compact interval.  This is the two-time family needed to obtain
an inverse by uniqueness; the initial time is genuine data, not an assumed
flow law. -/
theorem exists_twoTimeOdeTrajectoryOn_Icc_of_global_bounded_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (v : ℝ → E → E) (T K M : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (htime : ∀ x, ContinuousOn (fun t ↦ v t x) (Set.Icc (0 : ℝ) T))
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ M) :
    ∃ X : Set.Icc (0 : ℝ) T → E → ℝ → E, ∀ s x,
      X s x s = x ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (X s x) (v t (X s x t))
          (Set.Icc (0 : ℝ) T) t := by
  have hPL (s : Set.Icc (0 : ℝ) T) (x : E) : IsPicardLindelof
      (tmin := (0 : ℝ)) (tmax := (T : ℝ)) v s x (M * T) 0 M K := by
    refine {
      lipschitzOnWith := fun t _ht ↦ (hv t).lipschitzOnWith
      continuousOn := fun y _hy ↦ htime y
      norm_le := fun t ht y _hy ↦ hbound t ht y
      mul_max_le := ?_ }
    change (M : ℝ) * max ((T : ℝ) - s) (s - 0) ≤
      (M * T : NNReal) - 0
    simp only [NNReal.coe_mul, sub_zero]
    gcongr
    exact max_le (sub_le_self _ s.2.1) (by simpa using s.2.2)
  have hex (s : Set.Icc (0 : ℝ) T) (x : E) :=
    (hPL s x).exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose X hX using hex
  exact ⟨X, hX⟩

/-- Compact-interval two-time solutions obey the flow law.  The proof uses
right uniqueness after the intermediate time and time-reversed uniqueness
before it, so it also covers intermediate times at either endpoint. -/
theorem odeTrajectoryOn_Icc_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (T K : NNReal)
    (X : Set.Icc (0 : ℝ) T → E → ℝ → E)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X s x) (v t (X s x t))
        (Set.Icc (0 : ℝ) T) t)
    (hinit : ∀ s x, X s x s = x) :
    ∀ r s x (t : Set.Icc (0 : ℝ) T), X s (X r x s) t = X r x t := by
  intro r s x t
  have hcont (q : Set.Icc (0 : ℝ) T) (y : E) :
      ContinuousOn (X q y) (Set.Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn (fun u hu ↦ hX q y u hu)
  by_cases hst : s ≤ t
  · have htT : t ≤ (T : ℝ) := t.2.2
    have heq : Set.EqOn (X s (X r x s)) (X r x)
        (Set.Icc (s : ℝ) T) := by
      apply ODE_solution_unique_of_mem_Icc_right
          (s := fun _ ↦ Set.univ) (K := K) (v := v)
      · intro u _hu
        exact (hv u).lipschitzOnWith
      · exact (hcont s (X r x s)).mono (Set.Icc_subset_Icc s.2.1 le_rfl)
      · intro u hu
        apply (hX s (X r x s) u ⟨s.2.1.trans hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
        exact Icc_mem_nhdsGE_of_mem ⟨s.2.1.trans hu.1, hu.2⟩
      · simp
      · exact (hcont r x).mono (Set.Icc_subset_Icc s.2.1 le_rfl)
      · intro u hu
        apply (hX r x u ⟨s.2.1.trans hu.1, hu.2.le⟩).mono_of_mem_nhdsWithin
        exact Icc_mem_nhdsGE_of_mem ⟨s.2.1.trans hu.1, hu.2⟩
      · simp
      · exact hinit s (X r x s)
    exact heq ⟨hst, htT⟩
  · have hts : t ≤ s := le_of_not_ge hst
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have heq : Set.EqOn (X s (X r x s)) (X r x)
        (Set.Icc (0 : ℝ) s) := by
      apply ODE_solution_unique_of_mem_Icc_left
          (s := fun _ ↦ Set.univ) (K := K) (v := v)
      · intro u _hu
        exact (hv u).lipschitzOnWith
      · exact (hcont s (X r x s)).mono (Set.Icc_subset_Icc le_rfl s.2.2)
      · intro u hu
        apply (hX s (X r x s) u ⟨hu.1.le, hu.2.trans s.2.2⟩).mono_of_mem_nhdsWithin
        exact Icc_mem_nhdsLE_of_mem ⟨hu.1, hu.2.trans s.2.2⟩
      · simp
      · exact (hcont r x).mono (Set.Icc_subset_Icc le_rfl s.2.2)
      · intro u hu
        apply (hX r x u ⟨hu.1.le, hu.2.trans s.2.2⟩).mono_of_mem_nhdsWithin
        exact Icc_mem_nhdsLE_of_mem ⟨hu.1, hu.2.trans s.2.2⟩
      · simp
      · exact hinit s (X r x s)
    exact heq ⟨ht0, hts⟩

/-- Reversing a compact-interval two-time trajectory gives a two-sided inverse
on the interval. -/
theorem odeTrajectoryOn_Icc_leftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (T K : NNReal)
    (X : Set.Icc (0 : ℝ) T → E → ℝ → E)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X s x) (v t (X s x t))
        (Set.Icc (0 : ℝ) T) t)
    (hinit : ∀ s x, X s x s = x) :
    ∀ s t x, X t (X s x t) s = x := by
  intro s t x
  rw [odeTrajectoryOn_Icc_comp v T K X hv hX hinit s t x s, hinit]

/-- Every compact-interval time transition is bijective, with the reversed
transition as its actual inverse. -/
theorem odeTrajectoryOn_Icc_bijective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (T K : NNReal)
    (X : Set.Icc (0 : ℝ) T → E → ℝ → E)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X s x) (v t (X s x t))
        (Set.Icc (0 : ℝ) T) t)
    (hinit : ∀ s x, X s x s = x) :
    ∀ (s t : Set.Icc (0 : ℝ) T),
      Function.Bijective (fun x ↦ X s x t) := by
  intro s t
  have hleft : Function.LeftInverse (fun x ↦ X t x s) (fun x ↦ X s x t) :=
    fun x ↦ odeTrajectoryOn_Icc_leftInverse v T K X hv hX hinit s t x
  have hright : Function.RightInverse (fun x ↦ X t x s) (fun x ↦ X s x t) :=
    fun x ↦ odeTrajectoryOn_Icc_leftInverse v T K X hv hX hinit t s x
  exact ⟨hleft.injective, hright.surjective⟩

/-- Quantitative Grönwall estimate for the spatial variational equation.
The hypothesis is the uniform first-order remainder of the vector field along
nearby trajectories; it is strictly weaker than assuming the desired spatial
derivative of the flow. -/
theorem trajectory_variational_remainder_le_gronwall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : E → ℝ → E)
    (A J : ℝ → E →L[ℝ] E) (T K : NNReal) (x : E)
    (eta : E → NNReal)
    (hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u)
    (hzero : ∀ y, X y 0 = y)
    (hJ : ∀ h u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (fun q ↦ J q h) (A u (J u h))
        (Set.Icc (0 : ℝ) T) u)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hA : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖A u‖ ≤ K)
    (hremainder : ∀ h u, u ∈ Set.Icc (0 : ℝ) T →
      ‖v u (X (x + h) u) - v u (X x u) -
          A u (X (x + h) u - X x u)‖ ≤ eta h) :
    ∀ h u, u ∈ Set.Icc (0 : ℝ) T →
      ‖X (x + h) u - X x u - J u h‖ ≤
        gronwallBound 0 K (eta h) (u - 0) := by
  intro h u hu
  let R : ℝ → E := fun q ↦ X (x + h) q - X x q - J q h
  let R' : ℝ → E := fun q ↦
    v q (X (x + h) q) - v q (X x q) - A q (J q h)
  have hRcont : ContinuousOn R (Set.Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn (fun q hq ↦
      ((hX (x + h) q hq).sub (hX x q hq)).sub (hJ h q hq))
  have hRderiv : ∀ q ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt R (R' q) (Set.Ici q) q := by
    intro q hq
    apply (((hX (x + h) q ⟨hq.1, hq.2.le⟩).sub
      (hX x q ⟨hq.1, hq.2.le⟩)).sub
      (hJ h q ⟨hq.1, hq.2.le⟩)).mono_of_mem_nhdsWithin
    exact Icc_mem_nhdsGE_of_mem hq
  have hRzero : ‖R 0‖ ≤ 0 := by
    simp [R, hzero, hJzero]
  have hRbound : ∀ q ∈ Set.Ico (0 : ℝ) T,
      ‖R' q‖ ≤ (K : ℝ) * ‖R q‖ + (eta h : ℝ) := by
    intro q hq
    have hrem := hremainder h q ⟨hq.1, hq.2.le⟩
    have hlin : ‖A q (R q)‖ ≤ (K : ℝ) * ‖R q‖ := by
      calc
        ‖A q (R q)‖ ≤ ‖A q‖ * ‖R q‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (K : ℝ) * ‖R q‖ := by
          gcongr
          exact hA q ⟨hq.1, hq.2.le⟩
    calc
      ‖R' q‖ = ‖(v q (X (x + h) q) - v q (X x q) -
          A q (X (x + h) q - X x q)) + A q (R q)‖ := by
            congr 1
            simp only [R, R', map_sub]
            abel
      _ ≤ ‖v q (X (x + h) q) - v q (X x q) -
          A q (X (x + h) q - X x q)‖ + ‖A q (R q)‖ := norm_add_le _ _
      _ ≤ (eta h : ℝ) + (K : ℝ) * ‖R q‖ := add_le_add hrem hlin
      _ = (K : ℝ) * ‖R q‖ + (eta h : ℝ) := add_comm _ _
  exact norm_le_gronwallBound_of_norm_deriv_right_le
    hRcont hRderiv hRzero hRbound u hu

/-- A uniform little-o Taylor remainder for the vector field propagates
through the variational equation, so `J u` is the genuine Fréchet derivative
of the time-`u` trajectory map. -/
theorem hasFDerivAt_trajectory_of_variational_littleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : E → ℝ → E)
    (A J : ℝ → E →L[ℝ] E) (T K : NNReal) (x : E)
    (eta : E → NNReal)
    (hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u)
    (hzero : ∀ y, X y 0 = y)
    (hJ : ∀ h u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (fun q ↦ J q h) (A u (J u h))
        (Set.Icc (0 : ℝ) T) u)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hA : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖A u‖ ≤ K)
    (hremainder : ∀ h u, u ∈ Set.Icc (0 : ℝ) T →
      ‖v u (X (x + h) u) - v u (X x u) -
          A u (X (x + h) u - X x u)‖ ≤ eta h)
    (heta : (fun h ↦ (eta h : ℝ)) =o[nhds (0 : E)] (fun h ↦ h)) :
    ∀ u, u ∈ Set.Icc (0 : ℝ) T →
      HasFDerivAt (fun y ↦ X y u) (J u) x := by
  intro u hu
  let G : E → ℝ := fun h ↦ gronwallBound 0 K (eta h) (u - 0)
  have hG : G =o[nhds (0 : E)] (fun h ↦ h) := by
    by_cases hK : (K : ℝ) = 0
    · have hKnn : K = 0 := NNReal.eq hK
      subst K
      simpa [G, gronwallBound_K0, mul_comm] using heta.const_mul_left (u - 0)
    · let C : ℝ := (Real.exp ((K : ℝ) * (u - 0)) - 1) / (K : ℝ)
      have hscaled := heta.const_mul_left C
      apply hscaled.congr'
      · filter_upwards [] with h
        simp only [G, gronwallBound_of_K_ne_0 hK, zero_mul, zero_add]
        dsimp [C]
        ring
      · exact Filter.EventuallyEq.rfl
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [hG.bound hc] with h hh
  have hmain := trajectory_variational_remainder_le_gronwall
    v X A J T K x eta hX hzero hJ hJzero hA hremainder h u hu
  have hGnonneg : 0 ≤ G h := by
    calc
      0 = gronwallBound 0 K (eta h) 0 := (gronwallBound_x0 0 K (eta h)).symm
      _ ≤ gronwallBound 0 K (eta h) (u - 0) := by
        apply gronwallBound_mono (by positivity) (by positivity) (by positivity)
        simpa using hu.1
      _ = G h := rfl
  calc
    ‖X (x + h) u - X x u - J u h‖ ≤ G h := hmain
    _ = ‖G h‖ := (Real.norm_of_nonneg hGnonneg).symm
    _ ≤ c * ‖h‖ := by simpa using hh

/-- A globally Lipschitz Fréchet derivative gives a quadratic Taylor
remainder.  The constant `L` is intentionally not halved: this direct convex
segment estimate is the robust bound needed by the ODE argument. -/
theorem norm_taylor_remainder_le_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (D : E → E →L[ℝ] F) (L : NNReal)
    (hf : ∀ z, HasFDerivAt f (D z) z)
    (hD : LipschitzWith L D) (x y : E) :
    ‖f y - f x - D x (y - x)‖ ≤ (L : ℝ) * ‖y - x‖ ^ 2 := by
  have hseg := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := f) (f' := D) (φ := D x)
    (C := (L : ℝ) * ‖y - x‖)
    (fun z _hz ↦ (hf z).hasFDerivWithinAt)
    (fun z hz ↦ by
      calc
        ‖D z - D x‖ = dist (D z) (D x) := (dist_eq_norm _ _).symm
        _ ≤ (L : ℝ) * dist z x := hD.dist_le_mul z x
        _ = (L : ℝ) * ‖z - x‖ := by rw [dist_eq_norm]
        _ ≤ (L : ℝ) * ‖y - x‖ := by
          gcongr
          exact norm_sub_le_of_mem_segment hz)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  calc
    ‖f y - f x - D x (y - x)‖ ≤
        ((L : ℝ) * ‖y - x‖) * ‖y - x‖ := hseg
    _ = (L : ℝ) * ‖y - x‖ ^ 2 := by ring

/-- Spatial Lipschitz stability of compact-interval trajectories, with the
initial displacement propagated by the standard exponential Grönwall factor. -/
theorem odeTrajectoryOn_Icc_norm_sub_le_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : E → ℝ → E) (T K : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u)
    (hzero : ∀ y, X y 0 = y) :
    ∀ x y u, u ∈ Set.Icc (0 : ℝ) T →
      ‖X y u - X x u‖ ≤ ‖y - x‖ * Real.exp ((K : ℝ) * (u - 0)) := by
  intro x y u hu
  have hcont (z : E) : ContinuousOn (X z) (Set.Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn (fun q hq ↦ hX z q hq)
  have hright (z : E) : ∀ q ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (X z) (v q (X z q)) (Set.Ici q) q := by
    intro q hq
    apply (hX z q ⟨hq.1, hq.2.le⟩).mono_of_mem_nhdsWithin
    exact Icc_mem_nhdsGE_of_mem hq
  have hdist := dist_le_of_trajectories_ODE hv (hcont y) (hright y)
    (hcont x) (hright x) (a := (0 : ℝ)) (b := (T : ℝ))
    (δ := dist y x) (by simp [hzero]) u hu
  simpa only [dist_eq_norm] using hdist

/-- The spatial variational equation identifies the Fréchet derivative of a
compact-time flow when the vector field has a globally Lipschitz spatial
derivative.  All Taylor and trajectory-stability estimates are discharged
inside the theorem. -/
theorem hasFDerivAt_trajectory_of_lipschitz_fderiv_and_variational
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E)
    (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E)
    (T K L : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z)
    (hDv : ∀ t, LipschitzWith L (Dv t))
    (hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u)
    (hzero : ∀ y, X y 0 = y)
    (hJ : ∀ x h u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (fun q ↦ J x q h)
        (Dv u (X x u) (J x u h)) (Set.Icc (0 : ℝ) T) u)
    (hJzero : ∀ x, J x 0 = ContinuousLinearMap.id ℝ E) :
    ∀ x u, u ∈ Set.Icc (0 : ℝ) T →
      HasFDerivAt (fun y ↦ X y u) (J x u) x := by
  intro x u hu
  let A : ℝ → E →L[ℝ] E := fun q ↦ Dv q (X x q)
  let C : ℝ := (L : ℝ) * Real.exp ((K : ℝ) * (T : ℝ)) ^ 2
  let eta : E → NNReal := fun h ↦
    ⟨C * ‖h‖ ^ 2, mul_nonneg (by positivity) (sq_nonneg _)⟩
  have hAbound : ∀ q ∈ Set.Icc (0 : ℝ) T, ‖A q‖ ≤ K := by
    intro q _hq
    dsimp [A]
    rw [← (hvD q (X x q)).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hv q)
  have hrem : ∀ h q, q ∈ Set.Icc (0 : ℝ) T →
      ‖v q (X (x + h) q) - v q (X x q) -
          A q (X (x + h) q - X x q)‖ ≤ eta h := by
    intro h q hq
    have htaylor := norm_taylor_remainder_le_of_lipschitz_fderiv
      (v q) (Dv q) L (hvD q) (hDv q) (X x q) (X (x + h) q)
    have hflow := odeTrajectoryOn_Icc_norm_sub_le_exp
      v X T K hv hX hzero x (x + h) q hq
    have hexp : Real.exp ((K : ℝ) * (q - 0)) ≤
        Real.exp ((K : ℝ) * (T : ℝ)) := by
      apply Real.exp_le_exp.mpr
      gcongr
      simpa using hq.2
    calc
      ‖v q (X (x + h) q) - v q (X x q) -
          A q (X (x + h) q - X x q)‖ ≤
          (L : ℝ) * ‖X (x + h) q - X x q‖ ^ 2 := by
            simpa only [A] using htaylor
      _ ≤ (L : ℝ) *
          (‖(x + h) - x‖ * Real.exp ((K : ℝ) * (q - 0))) ^ 2 := by
            gcongr
      _ ≤ (L : ℝ) *
          (‖h‖ * Real.exp ((K : ℝ) * (T : ℝ))) ^ 2 := by
            simp only [add_sub_cancel_left]
            gcongr
      _ = (eta h : ℝ) := by
            change (L : ℝ) *
              (‖h‖ * Real.exp ((K : ℝ) * (T : ℝ))) ^ 2 = C * ‖h‖ ^ 2
            dsimp only [C]
            ring
  have heta : (fun h ↦ (eta h : ℝ)) =o[nhds (0 : E)] (fun h ↦ h) := by
    have hpow := Asymptotics.isLittleO_norm_pow_norm_pow (E' := E)
      (m := 1) (n := 2) (by omega)
    have hnorm : (fun h : E ↦ ‖h‖ ^ 2) =o[nhds (0 : E)] (fun h ↦ ‖h‖) := by
      simpa using hpow
    have hsquare : (fun h : E ↦ ‖h‖ ^ 2) =o[nhds (0 : E)] (fun h ↦ h) :=
      hnorm.of_norm_right
    have hscaled := hsquare.const_mul_left C
    apply hscaled.congr'
    · filter_upwards [] with h
      change C * ‖h‖ ^ 2 = C * ‖h‖ ^ 2
      rfl
    · exact Filter.EventuallyEq.rfl
  exact hasFDerivAt_trajectory_of_variational_littleO
    v X A (J x) T K x eta hX hzero
    (fun h q hq ↦ by simpa only [A] using hJ x h q hq)
    (hJzero x) hAbound hrem heta u hu

/-- A bounded continuous coefficient field has a matrix variational solution
on every interval short enough that `2*K*T ≤ 1`.  The solution is produced by
Picard--Lindelöf in the unit ball about the identity; no variational solution
is assumed. -/
theorem exists_variationalOn_Icc_of_two_mul_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (T K : NNReal)
    (hAcont : ContinuousOn A (Set.Icc (0 : ℝ) T))
    (hAnorm : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖A t‖ ≤ K)
    (hshort : (2 * K) * T ≤ 1) :
    ∃ J : ℝ → E →L[ℝ] E,
      J 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt J ((A t).comp (J t)) (Set.Icc (0 : ℝ) T) t := by
  let w : ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) :=
    fun t B ↦ (A t).comp B
  let t0 : Set.Icc (0 : ℝ) T := ⟨0, by simp⟩
  have hwLip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : LipschitzWith K (w t) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro B C
    change ‖(A t).comp B - (A t).comp C‖ ≤ (K : ℝ) * ‖B - C‖
    rw [← ContinuousLinearMap.comp_sub]
    calc
      ‖(A t).comp (B - C)‖ ≤ ‖A t‖ * ‖B - C‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖B - C‖ := by
        gcongr
        exact hAnorm t ht
  have hPL : IsPicardLindelof
      (tmin := (0 : ℝ)) (tmax := (T : ℝ)) w t0
      (ContinuousLinearMap.id ℝ E) 1 0 (2 * K) K := by
    refine {
      lipschitzOnWith := fun t ht ↦ (hwLip t ht).lipschitzOnWith
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
    · intro B _hB
      exact ((ContinuousLinearMap.compL ℝ E E E).flip B).continuous.comp_continuousOn
        hAcont
    · intro t ht B hB
      have hBdist : ‖B - ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hB
      have hBnorm : ‖B‖ ≤ 2 := by
        calc
          ‖B‖ = ‖(B - ContinuousLinearMap.id ℝ E) +
              ContinuousLinearMap.id ℝ E‖ := by congr 1; abel
          _ ≤ ‖B - ContinuousLinearMap.id ℝ E‖ +
              ‖ContinuousLinearMap.id ℝ E‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add hBdist ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      change ‖(A t).comp B‖ ≤ ((2 * K : NNReal) : ℝ)
      calc
        ‖(A t).comp B‖ ≤ ‖A t‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * 2 := mul_le_mul (hAnorm t ht) hBnorm (norm_nonneg _) (by positivity)
        _ = ((2 * K : NNReal) : ℝ) := by norm_num [mul_comm]
    · change (((2 * K) : NNReal) : ℝ) * max ((T : ℝ) - 0) (0 - 0) ≤
        ((1 : NNReal) : ℝ) - 0
      simpa using hshort
  simpa only [w] using hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- A globally defined ODE trajectory family inherits every additive period of
its velocity field.  This is the analytic kernel of lattice-equivariance for a
lifted torus flow; no equivariance of `X` is assumed. -/
theorem odeTrajectory_add_period
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : E → ℝ → E) (K : NNReal) (q : E)
    (hv : ∀ t, LipschitzWith K (v t))
    (hperiodic : ∀ t y, v t (y + q) = v t y)
    (hX : ∀ x t, HasDerivAt (X x) (v t (X x t)) t)
    (hzero : ∀ x, X x 0 = x) :
    ∀ x t, X (x + q) t = X x t + q := by
  intro x t
  have heq : X (x + q) = fun u ↦ X x u + q := by
    apply ODE_solution_unique_univ
        (s := fun _ ↦ Set.univ) (K := K) (v := v) (t₀ := 0)
    · intro u
      exact (hv u).lipschitzOnWith
    · intro u
      exact ⟨hX (x + q) u, Set.mem_univ _⟩
    · intro u
      constructor
      · simpa only [hperiodic] using (hX x u).add_const q
      · exact Set.mem_univ _
    · simp only [hzero]
  exact congrFun heq t

/-- Coordinatewise quotient from the Euclidean universal cover to the flat
unit two-torus. -/
def euclideanToTorus (x : ℝ × ℝ) : T2 :=
  ((x.1 : T1), (x.2 : T1))

/-- The coordinate quotient erases an integral lattice translation. -/
theorem euclideanToTorus_add_intPeriod (x : ℝ × ℝ) (q : ℤ × ℤ) :
    euclideanToTorus (x + ((q.1 : ℝ), (q.2 : ℝ))) = euclideanToTorus x := by
  ext <;> simp [euclideanToTorus]

/-- A complete trajectory family for a lattice-periodic velocity has a
representative-independent projection to `T2`.  This is the precise
well-definedness statement required before quotient descent. -/
theorem projectedOdeTrajectory_add_intPeriod
    (v : ℝ → (ℝ × ℝ) → (ℝ × ℝ))
    (X : (ℝ × ℝ) → ℝ → (ℝ × ℝ)) (K : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hperiodic : ∀ (q : ℤ × ℤ) t y,
      v t (y + ((q.1 : ℝ), (q.2 : ℝ))) = v t y)
    (hX : ∀ x t, HasDerivAt (X x) (v t (X x t)) t)
    (hzero : ∀ x, X x 0 = x) :
    ∀ (q : ℤ × ℤ) x t,
      euclideanToTorus (X (x + ((q.1 : ℝ), (q.2 : ℝ))) t) =
        euclideanToTorus (X x t) := by
  intro q x t
  rw [odeTrajectory_add_period v X K ((q.1 : ℝ), (q.2 : ℝ)) hv
    (hperiodic q) hX hzero x t]
  exact euclideanToTorus_add_intPeriod (X x t) q

/-- The canonical half-open representative of a point of the flat torus. -/
noncomputable def torusIcoRep (p : T2) : ℝ × ℝ :=
  ((AddCircle.equivIco (1 : ℝ) 0 p.1).1,
    (AddCircle.equivIco (1 : ℝ) 0 p.2).1)

@[simp]
theorem euclideanToTorus_torusIcoRep (p : T2) :
    euclideanToTorus (torusIcoRep p) = p := by
  ext <;> simp [euclideanToTorus, torusIcoRep]

/-- An actual torus-valued map obtained by projecting the Euclidean trajectory
from the canonical representative.  Lattice equivariance will show that this
agrees with the projection from every representative. -/
noncomputable def descendedOdeTrajectory
    (X : (ℝ × ℝ) → ℝ → (ℝ × ℝ)) (t : ℝ) : T2 → T2 :=
  fun p ↦ euclideanToTorus (X (torusIcoRep p) t)

/-- The descended trajectory starts at the identity whenever its Euclidean
lift starts at its initial point. -/
theorem descendedOdeTrajectory_zero
    (X : (ℝ × ℝ) → ℝ → (ℝ × ℝ))
    (hzero : ∀ x, X x 0 = x) :
    descendedOdeTrajectory X 0 = id := by
  funext p
  simp [descendedOdeTrajectory, hzero]

/-- The canonical unit-circle representative of a real point differs from that
real point by an integer. -/
theorem exists_int_add_eq_unitIcoRep (x : ℝ) :
    ∃ q : ℤ, (AddCircle.equivIco (1 : ℝ) 0 (x : T1)).1 = x + q := by
  let r : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (x : T1)).1
  have hcoe : (r : T1) = (x : T1) := by
    simp [r]
  have hzero : ((r - x : ℝ) : T1) = 0 := by
    rw [AddCircle.coe_sub, hcoe, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at hzero
  obtain ⟨q, hq⟩ := hzero
  refine ⟨q, ?_⟩
  change r = x + (q : ℝ)
  simpa using (eq_add_of_sub_eq' (by simpa using hq.symm))

/-- The canonical representative of a projected Euclidean point is an integral
lattice translate of the original point. -/
theorem exists_intPeriod_add_eq_torusIcoRep (x : ℝ × ℝ) :
    ∃ q : ℤ × ℤ,
      torusIcoRep (euclideanToTorus x) =
        x + ((q.1 : ℝ), (q.2 : ℝ)) := by
  obtain ⟨q₁, hq₁⟩ := exists_int_add_eq_unitIcoRep x.1
  obtain ⟨q₂, hq₂⟩ := exists_int_add_eq_unitIcoRep x.2
  refine ⟨(q₁, q₂), ?_⟩
  ext <;> simp [torusIcoRep, euclideanToTorus, hq₁, hq₂]

/-- The canonical-section definition of the descended trajectory agrees with
projecting the Euclidean trajectory from any representative. -/
theorem descendedOdeTrajectory_euclideanToTorus
    (v : ℝ → (ℝ × ℝ) → (ℝ × ℝ))
    (X : (ℝ × ℝ) → ℝ → (ℝ × ℝ)) (K : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hperiodic : ∀ (q : ℤ × ℤ) t y,
      v t (y + ((q.1 : ℝ), (q.2 : ℝ))) = v t y)
    (hX : ∀ x t, HasDerivAt (X x) (v t (X x t)) t)
    (hzero : ∀ x, X x 0 = x) :
    ∀ x t,
      descendedOdeTrajectory X t (euclideanToTorus x) =
        euclideanToTorus (X x t) := by
  intro x t
  obtain ⟨q, hq⟩ := exists_intPeriod_add_eq_torusIcoRep x
  rw [descendedOdeTrajectory, hq]
  exact projectedOdeTrajectory_add_intPeriod v X K hv hperiodic hX hzero q x t

/-- Complete solutions initialized at arbitrary starting times satisfy the
nonautonomous flow law.  The solution beginning at time `s` from the point
reached by a solution at time `s` is that original solution. -/
theorem odeTrajectory_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : ℝ → E → ℝ → E) (K : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ s x t, HasDerivAt (X s x) (v t (X s x t)) t)
    (hinit : ∀ s x, X s x s = x) :
    ∀ r s x t, X s (X r x s) t = X r x t := by
  intro r s x t
  have heq : X s (X r x s) = X r x := by
    apply ODE_solution_unique_univ
        (s := fun _ ↦ Set.univ) (K := K) (v := v) (t₀ := s)
    · intro u
      exact (hv u).lipschitzOnWith
    · intro u
      exact ⟨hX s (X r x s) u, Set.mem_univ _⟩
    · intro u
      exact ⟨hX r x u, Set.mem_univ _⟩
    · exact hinit s (X r x s)
  exact congrFun heq t

/-- Reversing the two-time trajectory gives a left inverse. -/
theorem odeTrajectory_leftInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ → E → E) (X : ℝ → E → ℝ → E) (K : NNReal)
    (hv : ∀ t, LipschitzWith K (v t))
    (hX : ∀ s x t, HasDerivAt (X s x) (v t (X s x t)) t)
    (hinit : ∀ s x, X s x s = x) :
    ∀ s t x, X t (X s x t) s = x := by
  intro s t x
  rw [odeTrajectory_comp v X K hv hX hinit s t x s, hinit]

/-- Liouville's determinant identity in the two-dimensional component form
needed by the torus flow.  A variational system with trace-free coefficient
matrix preserves determinant one. -/
theorem determinant_eq_one_of_traceFree_variational
    (a₁₁ a₁₂ a₂₁ a₂₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℝ → ℝ)
    (htrace : ∀ t, a₁₁ t + a₂₂ t = 0)
    (hJ₁₁ : ∀ t, HasDerivAt J₁₁
      (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t) t)
    (hJ₁₂ : ∀ t, HasDerivAt J₁₂
      (a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t) t)
    (hJ₂₁ : ∀ t, HasDerivAt J₂₁
      (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t) t)
    (hJ₂₂ : ∀ t, HasDerivAt J₂₂
      (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t) t)
    (hdet_zero : J₁₁ 0 * J₂₂ 0 - J₁₂ 0 * J₂₁ 0 = 1) :
    ∀ t, J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t = 1 := by
  let D : ℝ → ℝ := fun t ↦ J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t
  have hD : ∀ t, HasDerivAt D 0 t := by
    intro t
    have hd := (hJ₁₁ t).mul (hJ₂₂ t) |>.sub ((hJ₁₂ t).mul (hJ₂₁ t))
    have hcalc :
        (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t) * J₂₂ t +
            J₁₁ t * (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t) -
          ((a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t) * J₂₁ t +
            J₁₂ t * (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t)) = 0 := by
      calc
        _ = (a₁₁ t + a₂₂ t) *
            (J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t) := by ring
        _ = 0 := by rw [htrace t, zero_mul]
    simpa only [D, hcalc] using hd
  have hdiff : Differentiable ℝ D := fun t ↦ (hD t).differentiableAt
  have hconst : ∀ t, D t = D 0 := by
    intro t
    exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      hdiff.differentiableOn (fun u _ ↦ (hD u).deriv) (Set.mem_univ t) (Set.mem_univ 0)
  intro t
  change D t = 1
  rw [hconst t]
  exact hdet_zero

/-- Closed-interval form of the two-dimensional Liouville identity.  This
version retains the one-sided endpoint derivatives supplied directly by
Picard--Lindelöf. -/
theorem determinant_eq_one_of_traceFree_variationalOn_Icc
    (a₁₁ a₁₂ a₂₁ a₂₂ J₁₁ J₁₂ J₂₁ J₂₂ : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) T, a₁₁ t + a₂₂ t = 0)
    (hJ₁₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt J₁₁
      (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t) (Set.Icc (0 : ℝ) T) t)
    (hJ₁₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt J₁₂
      (a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t) (Set.Icc (0 : ℝ) T) t)
    (hJ₂₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt J₂₁
      (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t) (Set.Icc (0 : ℝ) T) t)
    (hJ₂₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt J₂₂
      (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t) (Set.Icc (0 : ℝ) T) t)
    (hdet_zero : J₁₁ 0 * J₂₂ 0 - J₁₂ 0 * J₂₁ 0 = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t = 1 := by
  let D : ℝ → ℝ := fun t ↦ J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t
  have hD : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt D 0 (Set.Icc (0 : ℝ) T) t := by
    intro t ht
    have hd := (hJ₁₁ t ht).mul (hJ₂₂ t ht) |>.sub
      ((hJ₁₂ t ht).mul (hJ₂₁ t ht))
    have hcalc :
        (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t) * J₂₂ t +
            J₁₁ t * (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t) -
          ((a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t) * J₂₁ t +
            J₁₂ t * (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t)) = 0 := by
      calc
        _ = (a₁₁ t + a₂₂ t) *
            (J₁₁ t * J₂₂ t - J₁₂ t * J₂₁ t) := by ring
        _ = 0 := by rw [htrace t ht, zero_mul]
    simpa only [D, hcalc] using hd
  have hdiff : DifferentiableOn ℝ D (Set.Icc (0 : ℝ) T) :=
    fun t ht ↦ (hD t ht).differentiableWithinAt
  have hderiv : Set.EqOn (derivWithin D (Set.Icc (0 : ℝ) T))
      (derivWithin (fun _ : ℝ ↦ (1 : ℝ)) (Set.Icc (0 : ℝ) T))
      (Set.Ico (0 : ℝ) T) := by
    intro t ht
    have htcc : t ∈ Set.Icc (0 : ℝ) T := Set.mem_Icc_of_Ico ht
    rw [(hD t htcc).derivWithin ((uniqueDiffOn_Icc hT) t htcc)]
    simp
  exact eq_of_derivWithin_eq hdiff
    (differentiableOn_const (c := (1 : ℝ))) hderiv hdet_zero

/-- Coordinate-free `Fin 2` form of Liouville's identity.  A continuous
linear-map variational solution driven by a trace-free coefficient has
determinant one. -/
theorem continuousLinearMap_det_eq_one_of_traceFree_variational
    (A J : ℝ → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (htrace : ∀ t,
      A t ![1, 0] 0 + A t ![0, 1] 1 = 0)
    (hJ : ∀ h t, HasDerivAt (fun q ↦ J q h) (A t (J t h)) t)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) :
    ∀ t, (J t).det = 1 := by
  let a₁₁ : ℝ → ℝ := fun t ↦ A t ![1, 0] 0
  let a₁₂ : ℝ → ℝ := fun t ↦ A t ![0, 1] 0
  let a₂₁ : ℝ → ℝ := fun t ↦ A t ![1, 0] 1
  let a₂₂ : ℝ → ℝ := fun t ↦ A t ![0, 1] 1
  let J₁₁ : ℝ → ℝ := fun t ↦ J t ![1, 0] 0
  let J₁₂ : ℝ → ℝ := fun t ↦ J t ![0, 1] 0
  let J₂₁ : ℝ → ℝ := fun t ↦ J t ![1, 0] 1
  let J₂₂ : ℝ → ℝ := fun t ↦ J t ![0, 1] 1
  have decomp (z : Fin 2 → ℝ) :
      z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext i
    fin_cases i <;> simp
  have apply_decomp (B : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
      (z : Fin 2 → ℝ) (i : Fin 2) :
      B z i = B ![1, 0] i * z 0 + B ![0, 1] i * z 1 := by
    rw [decomp z, map_add, map_smul, map_smul]
    simp [mul_comm]
  have hcomponent (h : Fin 2 → ℝ) (i : Fin 2) (t : ℝ) :
      HasDerivAt (fun q ↦ J q h i) (A t (J t h) i) t := by
    exact (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t (hJ h t)
  have hcol₀₀ (t : ℝ) : HasDerivAt J₁₁
      (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t) t := by
    convert hcomponent ![1, 0] 0 t using 1
    simpa [a₁₁, a₁₂, J₁₁, J₂₁] using
      (apply_decomp (A t) (J t ![1, 0]) 0).symm
  have hcol₁₀ (t : ℝ) : HasDerivAt J₁₂
      (a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t) t := by
    convert hcomponent ![0, 1] 0 t using 1
    simpa [a₁₁, a₁₂, J₁₂, J₂₂] using
      (apply_decomp (A t) (J t ![0, 1]) 0).symm
  have hcol₀₁ (t : ℝ) : HasDerivAt J₂₁
      (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t) t := by
    convert hcomponent ![1, 0] 1 t using 1
    simpa [a₂₁, a₂₂, J₁₁, J₂₁] using
      (apply_decomp (A t) (J t ![1, 0]) 1).symm
  have hcol₁₁ (t : ℝ) : HasDerivAt J₂₂
      (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t) t := by
    convert hcomponent ![0, 1] 1 t using 1
    simpa [a₂₁, a₂₂, J₁₂, J₂₂] using
      (apply_decomp (A t) (J t ![0, 1]) 1).symm
  have hdet0 : J₁₁ 0 * J₂₂ 0 - J₁₂ 0 * J₂₁ 0 = 1 := by
    simp [J₁₁, J₁₂, J₂₁, J₂₂, hJzero]
  have hdet := determinant_eq_one_of_traceFree_variational
    a₁₁ a₁₂ a₂₁ a₂₂ J₁₁ J₁₂ J₂₁ J₂₂
    (by simpa [a₁₁, a₂₂] using htrace)
    hcol₀₀ hcol₁₀ hcol₀₁ hcol₁₁ hdet0
  intro t
  have he₀ : (Pi.single 0 1 : Fin 2 → ℝ) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  have he₁ : (Pi.single 1 1 : Fin 2 → ℝ) = ![0, 1] := by
    funext i
    fin_cases i <;> simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' (J t).toLinearMap,
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply, he₀, he₁]
  simpa [J₁₁, J₁₂, J₂₁, J₂₂] using hdet t

/-- Coordinate-free closed-interval Liouville identity, matching the output
of `exists_variationalOn_Icc_of_two_mul_le_one`. -/
theorem continuousLinearMap_det_eq_one_of_traceFree_variationalOn_Icc
    (A J : ℝ → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (T : ℝ) (hT : 0 < T)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) T,
      A t ![1, 0] 0 + A t ![0, 1] 1 = 0)
    (hJ : ∀ (h : Fin 2 → ℝ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (fun q ↦ J q h) (A t (J t h))
        (Set.Icc (0 : ℝ) T) t)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ (Fin 2 → ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, (J t).det = 1 := by
  let a₁₁ : ℝ → ℝ := fun t ↦ A t ![1, 0] 0
  let a₁₂ : ℝ → ℝ := fun t ↦ A t ![0, 1] 0
  let a₂₁ : ℝ → ℝ := fun t ↦ A t ![1, 0] 1
  let a₂₂ : ℝ → ℝ := fun t ↦ A t ![0, 1] 1
  let J₁₁ : ℝ → ℝ := fun t ↦ J t ![1, 0] 0
  let J₁₂ : ℝ → ℝ := fun t ↦ J t ![0, 1] 0
  let J₂₁ : ℝ → ℝ := fun t ↦ J t ![1, 0] 1
  let J₂₂ : ℝ → ℝ := fun t ↦ J t ![0, 1] 1
  have decomp (z : Fin 2 → ℝ) :
      z = z 0 • ![1, 0] + z 1 • ![0, 1] := by
    funext i
    fin_cases i <;> simp
  have apply_decomp (B : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
      (z : Fin 2 → ℝ) (i : Fin 2) :
      B z i = B ![1, 0] i * z 0 + B ![0, 1] i * z 1 := by
    rw [decomp z, map_add, map_smul, map_smul]
    simp [mul_comm]
  have hcomponent (h : Fin 2 → ℝ) (i : Fin 2) (t : ℝ)
      (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivWithinAt (fun q ↦ J q h i) (A t (J t h) i)
        (Set.Icc (0 : ℝ) T) t := by
    exact (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivWithinAt t
      (hJ h t ht)
  have hcol₀₀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivWithinAt J₁₁ (a₁₁ t * J₁₁ t + a₁₂ t * J₂₁ t)
        (Set.Icc (0 : ℝ) T) t := by
    convert hcomponent ![1, 0] 0 t ht using 1
    simpa [a₁₁, a₁₂, J₁₁, J₂₁] using
      (apply_decomp (A t) (J t ![1, 0]) 0).symm
  have hcol₁₀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivWithinAt J₁₂ (a₁₁ t * J₁₂ t + a₁₂ t * J₂₂ t)
        (Set.Icc (0 : ℝ) T) t := by
    convert hcomponent ![0, 1] 0 t ht using 1
    simpa [a₁₁, a₁₂, J₁₂, J₂₂] using
      (apply_decomp (A t) (J t ![0, 1]) 0).symm
  have hcol₀₁ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivWithinAt J₂₁ (a₂₁ t * J₁₁ t + a₂₂ t * J₂₁ t)
        (Set.Icc (0 : ℝ) T) t := by
    convert hcomponent ![1, 0] 1 t ht using 1
    simpa [a₂₁, a₂₂, J₁₁, J₂₁] using
      (apply_decomp (A t) (J t ![1, 0]) 1).symm
  have hcol₁₁ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      HasDerivWithinAt J₂₂ (a₂₁ t * J₁₂ t + a₂₂ t * J₂₂ t)
        (Set.Icc (0 : ℝ) T) t := by
    convert hcomponent ![0, 1] 1 t ht using 1
    simpa [a₂₁, a₂₂, J₁₂, J₂₂] using
      (apply_decomp (A t) (J t ![0, 1]) 1).symm
  have hdet0 : J₁₁ 0 * J₂₂ 0 - J₁₂ 0 * J₂₁ 0 = 1 := by
    simp [J₁₁, J₁₂, J₂₁, J₂₂, hJzero]
  have hdet := determinant_eq_one_of_traceFree_variationalOn_Icc
    a₁₁ a₁₂ a₂₁ a₂₂ J₁₁ J₁₂ J₂₁ J₂₂ T hT
    (by intro t ht; simpa [a₁₁, a₂₂] using htrace t ht)
    hcol₀₀ hcol₁₀ hcol₀₁ hcol₁₁ hdet0
  intro t ht
  have he₀ : (Pi.single 0 1 : Fin 2 → ℝ) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  have he₁ : (Pi.single 1 1 : Fin 2 → ℝ) = ![0, 1] := by
    funext i
    fin_cases i <;> simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' (J t).toLinearMap,
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix'_apply, he₀, he₁]
  simpa [J₁₁, J₁₂, J₂₁, J₂₂] using hdet t ht

/-- A bijective differentiable map with unit absolute Jacobian determinant
preserves Lebesgue/Haar measure.  This packages Mathlib's higher-dimensional
change-of-variables theorem in exactly the form consumed by the flow bridge. -/
theorem measurePreserving_of_bijective_hasFDerivAt_abs_det_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (hbij : Function.Bijective f)
    (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hdet : ∀ x, |(f' x).det| = 1) :
    MeasurePreserving f mu mu := by
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x ↦ (hf x).continuousAt
  refine ⟨hcont.measurable, ?_⟩
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar
    mu (s := Set.univ) (f := f) (f' := f')
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ ↦ (hf x).hasFDerivWithinAt) hbij.1.injOn
  simpa [hdet, hbij.2.range_eq] using hmap

/-- A short compact-time flow of a `C¹,¹` trace-free planar vector field is
measure preserving.  The spatial derivative is constructed pointwise by the
matrix Picard theorem above; it is not an input to this statement. -/
theorem measurePreserving_odeTrajectory_endpoint_of_short
    (v : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (Dv : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (X : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ))
    (T K L : NNReal) (hT : 0 < T)
    (mu : Measure (Fin 2 → ℝ)) [Measure.IsAddHaarMeasure mu]
    (hv : ∀ t, LipschitzWith K (v t))
    (hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z)
    (hDv : ∀ t, LipschitzWith L (Dv t))
    (hAcont : ∀ x, ContinuousOn (fun t ↦ Dv t (X x t))
      (Set.Icc (0 : ℝ) T))
    (hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u)
    (hzero : ∀ y, X y 0 = y)
    (htrace : ∀ t z, Dv t z ![1, 0] 0 + Dv t z ![0, 1] 1 = 0)
    (hshort : (2 * K) * T ≤ 1)
    (hbij : Function.Bijective (fun x ↦ X x T)) :
    MeasurePreserving (fun x ↦ X x T) mu mu := by
  have hex : ∀ x : Fin 2 → ℝ,
      ∃ J : ℝ → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ),
        J 0 = ContinuousLinearMap.id ℝ (Fin 2 → ℝ) ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt J
            ((Dv t (X x t)).comp (J t)) (Set.Icc (0 : ℝ) T) t := by
    intro x
    apply exists_variationalOn_Icc_of_two_mul_le_one
      (fun t ↦ Dv t (X x t)) T K (hAcont x)
    · intro t _ht
      rw [← (hvD t (X x t)).fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ (hv t)
    · exact hshort
  choose J hJzero hJ using hex
  have hJeval : ∀ x h t, t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (fun q ↦ J x q h)
        (Dv t (X x t) (J x t h)) (Set.Icc (0 : ℝ) T) t := by
    intro x h t ht
    have heval :=
      (ContinuousLinearMap.apply ℝ (Fin 2 → ℝ) h).hasFDerivAt.comp_hasDerivWithinAt
        t (hJ x t ht)
    simpa using heval
  have hf : ∀ x u, u ∈ Set.Icc (0 : ℝ) T →
      HasFDerivAt (fun y ↦ X y u) (J x u) x :=
    hasFDerivAt_trajectory_of_lipschitz_fderiv_and_variational
      v Dv X J T K L hv hvD hDv hX hzero hJeval hJzero
  have hdet : ∀ x t, t ∈ Set.Icc (0 : ℝ) T → (J x t).det = 1 := by
    intro x
    exact continuousLinearMap_det_eq_one_of_traceFree_variationalOn_Icc
      (fun t ↦ Dv t (X x t)) (J x) T (by exact_mod_cast hT)
      (fun t ht ↦ htrace t (X x t)) (hJeval x) (hJzero x)
  have hTmem : (T : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨by positivity, le_rfl⟩
  apply measurePreserving_of_bijective_hasFDerivAt_abs_det_eq_one
    mu (fun x ↦ X x T) (fun x ↦ J x T) hbij
  · intro x
    exact hf x T hTmem
  · intro x
    rw [hdet x T hTmem, abs_one]

/-- Compact interface for the hypotheses of the short planar flow theorem.
Keeping this contract bundled also makes its strictly authenticated theorem
interface stable and small. -/
structure ShortPlanarFlowData (T K L : NNReal) where
  v : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)
  Dv : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)
  X : (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)
  hT : 0 < T
  hv : ∀ t, LipschitzWith K (v t)
  hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z
  hDv : ∀ t, LipschitzWith L (Dv t)
  hAcont : ∀ x, ContinuousOn (fun t ↦ Dv t (X x t))
    (Set.Icc (0 : ℝ) T)
  hX : ∀ y u, u ∈ Set.Icc (0 : ℝ) T →
    HasDerivWithinAt (X y) (v u (X y u)) (Set.Icc (0 : ℝ) T) u
  hzero : ∀ y, X y 0 = y
  htrace : ∀ t z, Dv t z ![1, 0] 0 + Dv t z ![0, 1] 1 = 0
  hshort : (2 * K) * T ≤ 1
  hbij : Function.Bijective (fun x ↦ X x T)

/-- Bundled, verifier-stable form of short-time volume preservation. -/
theorem ShortPlanarFlowData.measurePreserving_endpoint
    {T K L : NNReal} (D : ShortPlanarFlowData T K L)
    (mu : Measure (Fin 2 → ℝ)) [Measure.IsAddHaarMeasure mu] :
    MeasurePreserving (fun x ↦ D.X x T) mu mu := by
  exact measurePreserving_odeTrajectory_endpoint_of_short
    D.v D.Dv D.X T K L D.hT mu D.hv D.hvD D.hDv D.hAcont
    D.hX D.hzero D.htrace D.hshort D.hbij

/-- A named Euclidean plane type keeps downstream verifier interfaces from
expanding every product measurable-space instance. -/
abbrev EuclideanPlane := Fin 2 → ℝ

/-- Strict-receipt interface for the short-time measure-preservation result. -/
theorem ShortPlanarFlowData.measurePreserving_endpoint_plane
    {T K L : NNReal} (D : ShortPlanarFlowData T K L)
    (mu : Measure EuclideanPlane) [Measure.IsAddHaarMeasure mu] :
    MeasurePreserving (fun x : EuclideanPlane ↦ D.X x T) mu mu := by
  exact D.measurePreserving_endpoint mu

/-- Lebesgue-volume specialization with no expanded measure-class binder. -/
theorem ShortPlanarFlowData.measurePreserving_endpoint_volume
    {T K L : NNReal} (D : ShortPlanarFlowData T K L) :
    MeasurePreserving (fun x : EuclideanPlane ↦ D.X x T) := by
  exact D.measurePreserving_endpoint MeasureTheory.volume

/-- A genuine two-time compact flow contract.  Unlike `ShortPlanarFlowData`,
this structure stores no endpoint bijectivity; the reverse ODE transition
will produce it. -/
structure ShortTwoTimePlanarFlowData (T K L : NNReal) where
  v : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)
  Dv : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)
  Y : Set.Icc (0 : ℝ) T → (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)
  hT : 0 < T
  hv : ∀ t, LipschitzWith K (v t)
  hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z
  hDv : ∀ t, LipschitzWith L (Dv t)
  hAcont : ∀ x, ContinuousOn
    (fun t ↦ Dv t (Y ⟨0, by simp⟩ x t)) (Set.Icc (0 : ℝ) T)
  hY : ∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
    HasDerivWithinAt (Y s x) (v t (Y s x t)) (Set.Icc (0 : ℝ) T) t
  hinit : ∀ s x, Y s x s = x
  htrace : ∀ t z, Dv t z ![1, 0] 0 + Dv t z ![0, 1] 1 = 0
  hshort : (2 * K) * T ≤ 1

/-- The endpoint of a genuine short two-time planar flow preserves Lebesgue
volume; bijectivity is derived from the reversed transition. -/
theorem ShortTwoTimePlanarFlowData.measurePreserving_endpoint_volume
    {T K L : NNReal} (D : ShortTwoTimePlanarFlowData T K L) :
    MeasurePreserving
      (fun x : EuclideanPlane ↦ D.Y ⟨0, by simp⟩ x T) := by
  let s0 : Set.Icc (0 : ℝ) T := ⟨0, by simp⟩
  let sT : Set.Icc (0 : ℝ) T := ⟨T, by simp⟩
  let S : ShortPlanarFlowData T K L := {
    v := D.v
    Dv := D.Dv
    X := fun x t ↦ D.Y s0 x t
    hT := D.hT
    hv := D.hv
    hvD := D.hvD
    hDv := D.hDv
    hAcont := by simpa only [s0] using D.hAcont
    hX := fun y u hu ↦ D.hY s0 y u hu
    hzero := fun y ↦ D.hinit s0 y
    htrace := D.htrace
    hshort := D.hshort
    hbij := odeTrajectoryOn_Icc_bijective
      D.v T K D.Y D.hv D.hY D.hinit s0 sT }
  simpa only [S, s0, sT] using S.measurePreserving_endpoint_volume

/-- A full compact two-time planar flow, without a shortness restriction. -/
structure PlanarTwoTimeFlowData (T K L : NNReal) where
  v : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)
  Dv : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)
  Y : Set.Icc (0 : ℝ) T → (Fin 2 → ℝ) → ℝ → (Fin 2 → ℝ)
  hT : 0 < T
  hv : ∀ t, LipschitzWith K (v t)
  hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z
  hDv : ∀ t, LipschitzWith L (Dv t)
  hAcont : ∀ s x, ContinuousOn (fun t ↦ Dv t (Y s x t))
    (Set.Icc (0 : ℝ) T)
  hY : ∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
    HasDerivWithinAt (Y s x) (v t (Y s x t)) (Set.Icc (0 : ℝ) T) t
  hinit : ∀ s x, Y s x s = x
  htrace : ∀ t z, Dv t z ![1, 0] 0 + Dv t z ![0, 1] 1 = 0

/-- Every sufficiently short transition of a genuine full flow preserves
Lebesgue volume.  The proof rebases time to `[0,t-s]`. -/
theorem PlanarTwoTimeFlowData.measurePreserving_transition_of_short
    {T K L : NNReal} (D : PlanarTwoTimeFlowData T K L)
    (s t : Set.Icc (0 : ℝ) T) (δ : NNReal)
    (hδeq : (δ : ℝ) = (t : ℝ) - s) (hst : (s : ℝ) < t)
    (hshort : (2 * K) * δ ≤ 1) :
    MeasurePreserving (fun x : EuclideanPlane ↦ D.Y s x t) := by
  have hδ : 0 < δ := by
    exact_mod_cast (show 0 < (δ : ℝ) by rw [hδeq]; exact sub_pos.mpr hst)
  have hmaps : Set.MapsTo (fun q : ℝ ↦ (s : ℝ) + q)
      (Set.Icc (0 : ℝ) δ) (Set.Icc (0 : ℝ) T) := by
    intro q hq
    constructor
    · exact s.2.1.trans (le_add_of_nonneg_right hq.1)
    · calc
        (s : ℝ) + q ≤ (s : ℝ) + δ := by linarith [hq.2]
        _ = t := by rw [hδeq]; ring
        _ ≤ T := t.2.2
  let S : ShortPlanarFlowData δ K L := {
    v := fun q ↦ D.v ((s : ℝ) + q)
    Dv := fun q ↦ D.Dv ((s : ℝ) + q)
    X := fun x q ↦ D.Y s x ((s : ℝ) + q)
    hT := hδ
    hv := fun q ↦ D.hv ((s : ℝ) + q)
    hvD := fun q z ↦ D.hvD ((s : ℝ) + q) z
    hDv := fun q ↦ D.hDv ((s : ℝ) + q)
    hAcont := by
      intro x
      exact (D.hAcont s x).comp
        (continuous_const.add continuous_id).continuousOn hmaps
    hX := by
      intro x q hq
      have hi : HasDerivWithinAt (fun r : ℝ ↦ (s : ℝ) + r) 1
          (Set.Icc (0 : ℝ) δ) q := by
        simpa using ((hasDerivAt_const q (s : ℝ)).add
          (hasDerivAt_id q)).hasDerivWithinAt
      have ho := (D.hY s x ((s : ℝ) + q) (hmaps hq)).scomp q hi hmaps
      simpa only [Function.comp_apply, one_smul] using ho
    hzero := by
      intro x
      simpa using D.hinit s x
    htrace := fun q z ↦ D.htrace ((s : ℝ) + q) z
    hshort := hshort
    hbij := by
      have hb := odeTrajectoryOn_Icc_bijective
        D.v T K D.Y D.hv D.hY D.hinit s t
      convert hb using 1
      funext x
      rw [hδeq]
      ring }
  convert S.measurePreserving_endpoint_volume using 1
  funext x
  change D.Y s x t = D.Y s x ((s : ℝ) + δ)
  rw [hδeq]
  ring

/-- Finite composition removes the local smallness restriction whenever a
strict short partition of the compact time interval is supplied. -/
theorem PlanarTwoTimeFlowData.measurePreserving_endpoint_of_partition
    {T K L : NNReal} (D : PlanarTwoTimeFlowData T K L)
    (n : ℕ) (τ : ℕ → Set.Icc (0 : ℝ) T) (δ : ℕ → NNReal)
    (hτzero : τ 0 = ⟨0, by simp⟩)
    (hτend : τ n = ⟨T, by simp⟩)
    (hstrict : ∀ i < n, ((τ i : Set.Icc (0 : ℝ) T) : ℝ) < τ (i + 1))
    (hδeq : ∀ i < n, (δ i : ℝ) = (τ (i + 1) : ℝ) - τ i)
    (hshort : ∀ i < n, (2 * K) * δ i ≤ 1) :
    MeasurePreserving
      (fun x : EuclideanPlane ↦ D.Y ⟨0, by simp⟩ x T) := by
  have hind : ∀ k ≤ n,
      MeasurePreserving (fun x : EuclideanPlane ↦ D.Y (τ 0) x (τ k)) := by
    intro k
    induction k with
    | zero =>
        intro _hk
        convert MeasurePreserving.id (volume : Measure EuclideanPlane) using 1
        funext x
        exact D.hinit (τ 0) x
    | succ k ih =>
        intro hk
        have hklt : k < n := Nat.lt_of_succ_le hk
        have hprev : k ≤ n := (Nat.le_succ k).trans hk
        have hp := D.measurePreserving_transition_of_short
          (τ k) (τ (k + 1)) (δ k) (hδeq k hklt)
          (hstrict k hklt) (hshort k hklt)
        have hc := hp.comp (ih hprev)
        convert hc using 1
        funext x
        exact (odeTrajectoryOn_Icc_comp D.v T K D.Y D.hv D.hY D.hinit
          (τ 0) (τ k) x (τ (k + 1))).symm
  have hend := hind n le_rfl
  rw [hτzero, hτend] at hend
  exact hend

/-- The equal `n`-grid is an explicit admissible short partition. -/
theorem PlanarTwoTimeFlowData.measurePreserving_endpoint_of_uniform_partition
    {T K L : NNReal} (D : PlanarTwoTimeFlowData T K L)
    (n : ℕ) (hn : 0 < n)
    (hshort : (2 * K) * (T / (n : NNReal)) ≤ 1) :
    MeasurePreserving
      (fun x : EuclideanPlane ↦ D.Y ⟨0, by simp⟩ x T) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let τ : ℕ → Set.Icc (0 : ℝ) T := fun i ↦
    ⟨(T : ℝ) * (Nat.min i n : ℝ) / n, by
      constructor
      · positivity
      · have hmin : (Nat.min i n : ℝ) ≤ n := by
          exact_mod_cast Nat.min_le_right i n
        calc
          (T : ℝ) * (Nat.min i n : ℝ) / n ≤ (T : ℝ) * n / n := by
            gcongr
          _ = T := by field_simp ⟩
  let δ : ℕ → NNReal := fun _ ↦ T / (n : NNReal)
  apply D.measurePreserving_endpoint_of_partition n τ δ
  · apply Subtype.ext
    simp [τ]
  · apply Subtype.ext
    simp [τ]
    field_simp
  · intro i hi
    change (T : ℝ) * (Nat.min i n : ℝ) / n <
      (T : ℝ) * (Nat.min (i + 1) n : ℝ) / n
    simp only [Nat.min_eq_left hi.le,
      Nat.min_eq_left (Nat.succ_le_of_lt hi)]
    apply div_lt_div_of_pos_right _ hnR
    apply mul_lt_mul_of_pos_left _
    · exact_mod_cast D.hT
    · exact_mod_cast Nat.lt_succ_self i
  · intro i hi
    change ((T / (n : NNReal) : NNReal) : ℝ) =
      (T : ℝ) * (Nat.min (i + 1) n : ℝ) / n -
        (T : ℝ) * (Nat.min i n : ℝ) / n
    simp only [Nat.min_eq_left hi.le,
      Nat.min_eq_left (Nat.succ_le_of_lt hi)]
    push_cast
    field_simp
    ring
  · intro i _hi
    exact hshort

/-- Every genuine compact planar flow satisfying the stated `C¹,¹` and
trace-free hypotheses preserves Lebesgue volume, with no smallness assumption
on `K*T`. -/
theorem PlanarTwoTimeFlowData.measurePreserving_endpoint
    {T K L : NNReal} (D : PlanarTwoTimeFlowData T K L) :
    MeasurePreserving
      (fun x : EuclideanPlane ↦ D.Y ⟨0, by simp⟩ x T) := by
  obtain ⟨n, hnlarge⟩ := exists_nat_gt ((((2 * K) * T : NNReal) : ℝ))
  have hn : 0 < n := by
    have hnonneg : (0 : ℝ) ≤ (((2 * K) * T : NNReal) : ℝ) := by positivity
    exact_mod_cast hnonneg.trans_lt hnlarge
  have hbound : (2 * K) * T ≤ (n : NNReal) := by
    exact_mod_cast hnlarge.le
  apply D.measurePreserving_endpoint_of_uniform_partition n hn
  rw [show (2 * K) * (T / (n : NNReal)) =
    ((2 * K) * T) / (n : NNReal) by ring]
  apply (div_le_one₀ ?_).2
  · exact hbound
  · exact_mod_cast hn

/-- Concrete analytic input for producing a planar incompressible flow.  In
particular, this contract contains the velocity field and its derivative, but
does not contain trajectories, a flow law, or measure preservation. -/
structure SmoothPlanarVelocityData (T K L M : NNReal) where
  v : ℝ → EuclideanPlane → EuclideanPlane
  Dv : ℝ → EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane
  hT : 0 < T
  hv : ∀ t, LipschitzWith K (v t)
  hvTime : ∀ x, ContinuousOn (fun t ↦ v t x) (Set.Icc (0 : ℝ) T)
  hvBound : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖v t x‖ ≤ M
  hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z
  hDv : ∀ t, LipschitzWith L (Dv t)
  hDvJoint : Continuous (Function.uncurry Dv)
  htrace : ∀ t z, Dv t z ![1, 0] 0 + Dv t z ![0, 1] 1 = 0

/-- A bounded globally spatially Lipschitz `C¹,¹` planar velocity produces
a genuine two-time compact flow.  The flow law and inverse are consequences
of ODE uniqueness in the downstream `PlanarTwoTimeFlowData` API. -/
theorem SmoothPlanarVelocityData.exists_planarTwoTimeFlowData
    {T K L M : NNReal} (D : SmoothPlanarVelocityData T K L M) :
    ∃ F : PlanarTwoTimeFlowData T K L, F.v = D.v := by
  obtain ⟨Y, hY⟩ := exists_twoTimeOdeTrajectoryOn_Icc_of_global_bounded_lipschitz
    D.v T K M D.hv D.hvTime D.hvBound
  refine ⟨{
    v := D.v
    Dv := D.Dv
    Y := Y
    hT := D.hT
    hv := D.hv
    hvD := D.hvD
    hDv := D.hDv
    hAcont := ?_
    hY := fun s x t ht ↦ (hY s x).2 t ht
    hinit := fun s x ↦ (hY s x).1
    htrace := D.htrace }, rfl⟩
  intro s x
  have hYcont : ContinuousOn (Y s x) (Set.Icc (0 : ℝ) T) :=
    HasDerivWithinAt.continuousOn (fun t ht ↦ (hY s x).2 t ht)
  have hpair : ContinuousOn (fun t ↦ (t, Y s x t)) (Set.Icc (0 : ℝ) T) :=
    continuousOn_id.prodMk hYcont
  exact D.hDvJoint.comp_continuousOn hpair

/-- Direct producer-to-conservation theorem: every endpoint generated by the
velocity-only contract preserves planar Lebesgue volume. -/
theorem SmoothPlanarVelocityData.exists_measurePreserving_endpoint
    {T K L M : NNReal} (D : SmoothPlanarVelocityData T K L M) :
    ∃ Y : Set.Icc (0 : ℝ) T → EuclideanPlane → ℝ → EuclideanPlane,
      (∀ s x, Y s x s = x) ∧
      (∀ s x t, t ∈ Set.Icc (0 : ℝ) T →
        HasDerivWithinAt (Y s x) (D.v t (Y s x t))
          (Set.Icc (0 : ℝ) T) t) ∧
      MeasurePreserving (fun x : EuclideanPlane ↦ Y ⟨0, by simp⟩ x T) := by
  obtain ⟨F, hv⟩ := D.exists_planarTwoTimeFlowData
  refine ⟨F.Y, F.hinit, ?_, F.measurePreserving_endpoint⟩
  simpa only [hv] using F.hY

#print axioms exists_odeTrajectoryOn_Icc_of_global_bounded_lipschitz

end Bressan

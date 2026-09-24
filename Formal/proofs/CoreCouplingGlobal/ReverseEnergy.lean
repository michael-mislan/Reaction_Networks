import proofs.CoreCouplingGlobal.PhysicalUnstable

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology

theorem vector_energy_derivative (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → ResponseVector) (t : ℝ)
    (hd : HasDerivAt Y (responseVectorField e (Y t)) t)
    (hb : InResponseBox (decodeState (Y t))) :
    ∃ v : ℝ, HasDerivAt (fun u => statePotential e p (decodeState (Y u))) v t ∧
      v ≤ -responseResidualNorm e (decodeState (Y t)) := by
  let X := fun u => decodeState (Y u)
  have dA : HasDerivAt (fun u => (X u).A) (fA (flagshipRates e) (X t).A (X t).B (X t).z) t :=
    hasDerivAt_pi.mp hd 0
  have dB : HasDerivAt (fun u => (X u).B) (fB (flagshipRates e) (X t).A (X t).B (X t).z) t :=
    hasDerivAt_pi.mp hd 1
  have dz : HasDerivAt (fun u => (X u).z) (fZ (flagshipRates e) (X t).A (X t).B (X t).z (X t).H) t :=
    hasDerivAt_pi.mp hd 2
  have dH : HasDerivAt (fun u => (X u).H) (fH (flagshipRates e) (X t).z (X t).H) t :=
    hasDerivAt_pi.mp hd 3
  obtain ⟨hA,hA',hB,hB',hz,hz',hH,hH'⟩ := hb
  have dr := (dA.add dB).sub
    ((responseTotal_hasDerivAt e (X t).B he he' hB hB').comp t dB)
  have hv := responsePotential_hasDerivAt e p he he'
    (fun s => (X s).B) (fun s => (X s).z) (fun s => (X s).H)
    (fun s => (X s).A+(X s).B-responseTotal e (X s).B) t _ _ _ _
    ⟨hB,hB'⟩ ⟨hz,hz'⟩ ⟨hH,hH'⟩ dB dz dH dr
  refine ⟨_,hv,?_⟩
  have hh := response_directional_dissipation e (X t).A (X t).B (X t).z (X t).H
    he he' hA hA' hB hB' hz hz' hH hH'
  dsimp [responseResidualNorm]
  convert hh using 1
  ring


theorem reversed_vector_energy_derivative (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (Y : ℝ → ResponseVector) (t : ℝ)
    (hd : HasDerivAt Y (-responseVectorField e (Y t)) t)
    (hb : InResponseBox (decodeState (Y t))) :
    ∃ v : ℝ, HasDerivAt (fun u => statePotential e p (decodeState (Y u))) v t ∧
      responseResidualNorm e (decodeState (Y t)) ≤ v := by
  have hrev : HasDerivAt (fun u => Y (-u)) (responseVectorField e (Y t)) (-t) := by
    have hd' : HasDerivAt Y (-responseVectorField e (Y t)) (-(-t)) := by simpa using hd
    have h := hd'.scomp (-t) (hasDerivAt_id (-t)).neg
    simpa using h
  obtain ⟨v,hv,hbound⟩ := vector_energy_derivative e p he hu (fun u => Y (-u)) (-t)
    (by simpa using hrev) (by simpa using hb)
  refine ⟨-v,?_,?_⟩
  · have h := hv.comp t (hasDerivAt_id t).neg
    simpa [Function.comp_def] using h
  · simpa using neg_le_neg hbound

/-- A nondecreasing function with positive initial slope lies strictly below
its finite limit. This uses no infinite-time integral or quantitative decay. -/
theorem initial_lt_limit_of_monotone_positive_derivative (V : ℝ → ℝ) (L d : ℝ)
    (hm : MonotoneOn V (Ici 0)) (hl : Tendsto V atTop (𝓝 L))
    (hd : HasDerivAt V d 0) (hdpos : 0 < d) : V 0 < L := by
  have hle : ∀ t, 0 ≤ t → V t ≤ L := by
    intro t ht
    apply ge_of_tendsto hl
    filter_upwards [eventually_ge_atTop t] with u hu
    exact hm ht (ht.trans hu) hu
  apply lt_of_le_of_ne (hle 0 le_rfl)
  intro heq
  have hequal : ∀ t ∈ Ici (0:ℝ), V t=L := by
    intro t ht
    exact le_antisymm (hle t ht) (heq ▸ hm (by simp) ht ht)
  have hc : HasDerivWithinAt V 0 (Ici 0) 0 :=
    (hasDerivAt_const (0:ℝ) L).hasDerivWithinAt.congr hequal heq
  have hz := hc.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hz' := hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  linarith

/-- Actual backward convergence forces strict energy below the middle at every
nonstationary starting point, provided the backward path lies in the response box. -/
theorem reversed_trajectory_strict_sublevel (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (Y : ℝ → ResponseVector)
    (hd : ∀ t, 0 ≤ t → HasDerivAt Y (-responseVectorField e (Y t)) t)
    (hb : ∀ t, 0 ≤ t → InResponseBox (decodeState (Y t)))
    (s : State) (hs : InResponseBox s)
    (hl : Tendsto Y atTop (𝓝 (encodeState s)))
    (hns : ¬ Stationary (flagshipRates e) (decodeState (Y 0))) :
    statePotential e p (decodeState (Y 0)) < statePotential e p s := by
  let V := fun t => statePotential e p (decodeState (Y t))
  have hder := fun t ht => reversed_vector_energy_derivative e p he hu Y t (hd t ht) (hb t ht)
  have hmono : MonotoneOn V (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht
      exact (hder t ht).choose_spec.1.continuousAt.continuousWithinAt
    · intro t ht
      exact (hder t (interior_subset ht)).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro t ht
      obtain ⟨v,hv,hbound⟩ := hder t (interior_subset ht)
      rw [hv.deriv]
      exact (responseResidualNorm_nonneg e _).trans hbound
  have hmem : ∀ᶠ t in atTop, Y t ∈ responseBox := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (responseBox_iff _).2 (hb t ht)
  have hsmem : encodeState s ∈ responseBox := (responseBox_iff _).2 (by simpa using hs)
  have hwithin : Tendsto Y atTop (𝓝[responseBox] (encodeState s)) :=
    tendsto_nhdsWithin_iff.2 ⟨hl,hmem⟩
  have hvlim : Tendsto V atTop (𝓝 (statePotential e p s)) := by
    simpa only [V,Function.comp_apply,decode_encodeState] using
      ((statePotential_continuousOn e p) _ hsmem).tendsto.comp hwithin
  obtain ⟨v,hv,hbound⟩ := hder 0 le_rfl
  have hrpos : 0 < responseResidualNorm e (decodeState (Y 0)) := by
    apply lt_of_le_of_ne (responseResidualNorm_nonneg e _)
    intro hz
    exact hns (stationary_of_responseResidualNorm_zero e _ he hu (hb 0 le_rfl) hz.symm)
  exact initial_lt_limit_of_monotone_positive_derivative V _ v hmono hvlim hv
    (hrpos.trans_le hbound)

end CoreCouplingGlobal

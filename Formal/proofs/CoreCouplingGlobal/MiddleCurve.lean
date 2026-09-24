import proofs.CoreCouplingGlobal.BasinTopology

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

noncomputable def responseCurveState (e z : ℝ) : State :=
  ⟨responseA e (60/(z+2)),60/(z+2),z,naturalH z⟩

theorem responseCurveState_energy (e : ℝ) (p : PotentialPrimitives e) (z : ℝ) :
    statePotential e p (responseCurveState e z) = curveEnergy e p z := by
  dsimp [statePotential,responseCurveState,curveEnergy,responseTotal,responsePotential]
  ring

theorem responseCurveState_stationary (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    responseCurveState e s.z = s := by
  obtain ⟨hr,hH,_⟩ := positive_stationary_barrier_identities e he hu s hs hss
  have ha := hss.1
  have hb := hss.2.1
  dsimp [fA,fB,flagshipRates] at ha hb
  have hB : s.B = 60/(s.z+2) := by
    apply (eq_div_iff (by have := hs.2.2.1; positivity : s.z+2 ≠ 0)).2
    linear_combination -ha-2*hb
  have hA : s.A = responseA e (60/(s.z+2)) := by
    dsimp [responseTotal] at hr
    rw [hB] at hr
    linarith
  cases s
  simp_all only [responseCurveState]

theorem responseCurveState_continuousAt (e z : ℝ) (hz : 0 ≤ z) :
    ContinuousAt (fun t => encodeState (responseCurveState e t)) z := by
  have hc : ContinuousAt (fun t : ℝ => 60/(t+2)) z :=
    continuousAt_const.div (continuousAt_id.add continuousAt_const) (by positivity)
  apply continuousAt_pi.2
  intro i
  fin_cases i
  · exact (responseA_continuous e).continuousAt.comp hc
  · exact hc
  · exact continuousAt_id
  · change ContinuousAt naturalH z
    unfold naturalH
    fun_prop

theorem curveEnergy_strict_increase (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (x y : ℝ)
    (hx : 9/10 ≤ x) (hy : y ≤ 31/10) (hxy : x < y)
    (hpos : ∀ t ∈ Ioo x y, 0 < residual (varyRates e) t) :
    curveEnergy e p x < curveEnergy e p y := by
  let df := fun z => -reducedZ e (60/(z+2)) z/((z+1)*(z+2))
  obtain ⟨t,ht,heSlope⟩ := exists_hasDerivAt_eq_slope (curveEnergy e p) df hxy
    (fun t ht => (curveEnergy_hasDerivAt e p he hu t
      ⟨le_trans hx ht.1,le_trans ht.2 hy⟩).continuousAt.continuousWithinAt)
    (fun t ht => curveEnergy_hasDerivAt e p he hu t
      ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hd : 0 < df t := (curveEnergy_derivative_sign e t he hu
    ⟨by linarith [ht.1],by linarith [ht.2]⟩).1.2 (hpos t ht)
  have hmul := mul_pos hd (sub_pos.mpr hxy)
  have hid := (eq_div_iff (by linarith : y-x ≠ 0)).1 heSlope
  nlinarith

theorem curveEnergy_strict_decrease (e : ℝ) (p : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (x y : ℝ)
    (hx : 9/10 ≤ x) (hy : y ≤ 31/10) (hxy : x < y)
    (hneg : ∀ t ∈ Ioo x y, residual (varyRates e) t < 0) :
    curveEnergy e p y < curveEnergy e p x := by
  let df := fun z => -reducedZ e (60/(z+2)) z/((z+1)*(z+2))
  obtain ⟨t,ht,heSlope⟩ := exists_hasDerivAt_eq_slope (curveEnergy e p) df hxy
    (fun t ht => (curveEnergy_hasDerivAt e p he hu t
      ⟨le_trans hx ht.1,le_trans ht.2 hy⟩).continuousAt.continuousWithinAt)
    (fun t ht => curveEnergy_hasDerivAt e p he hu t
      ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hd : df t < 0 := (curveEnergy_derivative_sign e t he hu
    ⟨by linarith [ht.1],by linarith [ht.2]⟩).2.2 (hneg t ht)
  have hmul := mul_neg_of_neg_of_pos hd (sub_pos.mpr hxy)
  have hid := (eq_div_iff (by linarith : y-x ≠ 0)).1 heSlope
  nlinarith

end CoreCouplingGlobal

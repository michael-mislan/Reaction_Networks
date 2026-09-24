import proofs.CoreCouplingGlobal.ConeDestinations
import proofs.CoreCouplingGlobal.BasinTopology

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

noncomputable def responseState (e : ℝ) (x : SaddleVector) : State :=
  ⟨responseA e (x 0)+x 3,x 0,x 1,x 2⟩

theorem saddleCoordinates_responseState (e : ℝ) (x : SaddleVector) :
    saddleCoordinates e (responseState e x) = x := by
  ext i
  fin_cases i <;> simp [saddleCoordinates,responseState,responseTotal]
  ring

theorem responseState_saddleCoordinates (e : ℝ) (s : State) :
    responseState e (saddleCoordinates e s) = s := by
  cases s
  simp [responseState,saddleCoordinates,responseTotal]
  ring

theorem responseState_continuous (e : ℝ) :
    Continuous (fun x : SaddleVector => encodeState (responseState e x)) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact ((responseA_continuous e).comp (continuous_apply 0)).add (continuous_apply 3)
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2

theorem perturbedSaddleQuadratic_smul (e z α t : ℝ) (v : SaddleVector) :
    perturbedSaddleQuadratic e z α (t • v) = t^2*perturbedSaddleQuadratic e z α v := by
  simp [perturbedSaddleQuadratic,saddleQuadraticValue,responseQuadratic,
    saddlePairing,Fin.sum_univ_succ]
  ring

/-- Every negative response direction gives actual positive states arbitrarily
close in physical and response coordinates. -/
theorem positive_response_perturbation (e z α : ℝ) (s : State) (hs : s.Positive)
    (v : SaddleVector) (hv : perturbedSaddleQuadratic e z α v < 0)
    (ε ρ : ℝ) (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ t : ℝ, 0 < t ∧ ∃ y : State, y.Positive ∧
      dist (encodeState y) (encodeState s) < ε ∧
      dist (saddleCoordinates e y) (saddleCoordinates e s) < ρ ∧
      saddleCoordinates e y = saddleCoordinates e s+t • v ∧
      perturbedSaddleQuadratic e z α (saddleCoordinates e s-saddleCoordinates e y) < 0 := by
  let c : ℝ → SaddleVector := fun t => saddleCoordinates e s+t • v
  let f : ℝ → ResponseVector := fun t => encodeState (responseState e (c t))
  have hc : Continuous c := continuous_const.add (continuous_id.smul continuous_const)
  have hf : Continuous f := (responseState_continuous e).comp hc
  have hc0 : c 0 = saddleCoordinates e s := by simp [c]
  have hf0 : f 0 = encodeState s := by simp [f,hc0,responseState_saddleCoordinates]
  have hp : ∀ᶠ t in 𝓝 (0:ℝ), f t ∈ positiveDomain :=
    hf.continuousAt.eventually (positiveDomain_isOpen.mem_nhds (by
      simpa only [hf0,positiveDomain,mem_setOf_eq,decode_encodeState] using hs))
  have heps : ∀ᶠ t in 𝓝 (0:ℝ), dist (f t) (encodeState s) < ε := by
    have hh := hf.continuousAt.eventually (Metric.ball_mem_nhds (f 0) hε)
    simpa only [hf0,Metric.mem_ball] using hh
  have hrho : ∀ᶠ t in 𝓝 (0:ℝ), dist (c t) (saddleCoordinates e s) < ρ := by
    have hh := hc.continuousAt.eventually (Metric.ball_mem_nhds (c 0) hρ)
    simpa only [hc0,Metric.mem_ball] using hh
  obtain ⟨d,hd,hall⟩ := Metric.eventually_nhds_iff.mp (hp.and (heps.and hrho))
  let t := d/2
  have ht : 0 < t := by dsimp [t]; positivity
  have htd : dist t 0 < d := by rw [Real.dist_eq,sub_zero,abs_of_pos ht]; dsimp [t]; linarith
  obtain ⟨hy,hphys,hresp⟩ := hall htd
  refine ⟨t,ht,responseState e (c t),?_,hphys,?_,?_,?_⟩
  · simpa only [f,positiveDomain,mem_setOf_eq,decode_encodeState] using hy
  · simpa only [saddleCoordinates_responseState] using hresp
  · exact saddleCoordinates_responseState e (c t)
  · rw [saddleCoordinates_responseState]
    have hdiff : saddleCoordinates e s-c t = (-t) • v := by
      dsimp [c]
      module
    rw [hdiff,perturbedSaddleQuadratic_smul]
    exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (neg_ne_zero.mpr ht.ne')) hv

/-- Every sufficiently close reference trajectory has arbitrarily close
positive initial states selecting each of the two outer equilibria. -/
theorem nearby_reference_two_destinations (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
      Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
      Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
      ∃ η : ℝ, 0 < η ∧ ∀ X : ℝ → State, IsPositiveTrajectory e X →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) (saddleCoordinates e mid) < η) →
      ∀ ε : ℝ, 0 < ε →
      ∃ Y Z : ℝ → State, IsPositiveTrajectory e Y ∧ IsPositiveTrajectory e Z ∧
        dist (encodeState (Y 0)) (encodeState (X 0)) < ε ∧
        dist (encodeState (Z 0)) (encodeState (X 0)) < ε ∧
        Tendsto (fun t => encodeState (Y t)) atTop (𝓝 (encodeState low)) ∧
        Tendsto (fun t => encodeState (Z t)) atTop (𝓝 (encodeState high)) := by
  obtain ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,hbm,
    α,δ,θ,hα,hδ,hθ,hv,hselect⟩ := middle_cone_departures_select e hl hu
  let r := δ/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrd : r < δ := by dsimp [r]; linarith
  let η := min (θ*r) (r/2)
  have hη : 0 < η := lt_min (mul_pos hθ hr) (half_pos hr)
  refine ⟨low,mid,high,hlo,hm,hhi,hslo,hsm,hshi,hlm,hmh,η,hη,?_⟩
  intro X hX hstay ε hε
  let v : SaddleVector :=
    ![-(60/(mid.z+2))/(mid.z+2),1,(16+4*mid.z)/(20001/10000),0]
  have hv0 : v 0 < 0 := by
    change -(60/(mid.z+2))/(mid.z+2) < 0
    have hz : 0 < mid.z+2 := by linarith [hbm.1]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos (by norm_num) hz)) hz
  have hv' : perturbedSaddleQuadratic e mid.z α ((-1:ℝ) • v) < 0 := by
    rw [perturbedSaddleQuadratic_smul]
    simpa using hv
  obtain ⟨a,ha,s,hs,hsε,hsρ,hsc,hsq⟩ :=
    positive_response_perturbation e mid.z α (X 0) (hX.positive 0 le_rfl)
      v hv ε (r/2) hε (half_pos hr)
  obtain ⟨b,hb,w,hw,hwε,hwρ,hwc,hwq⟩ :=
    positive_response_perturbation e mid.z α (X 0) (hX.positive 0 le_rfl)
      ((-1:ℝ) • v) hv' ε (r/2) hε (half_pos hr)
  obtain ⟨Y,hY0,hY⟩ := positive_global_solution e (by linarith) hu w hw
  obtain ⟨Z,hZ0,hZ⟩ := positive_global_solution e (by linarith) hu s hs
  have hstayθ : ∀ t : ℝ, 0 ≤ t →
      dist (saddleCoordinates e (X t)) (saddleCoordinates e mid) < θ*r :=
    fun t ht => lt_of_lt_of_le (hstay t ht) (min_le_left _ _)
  have hXr : dist (saddleCoordinates e (X 0)) (saddleCoordinates e mid) < r/2 :=
    lt_of_lt_of_le (hstay 0 le_rfl) (min_le_right _ _)
  have hsr : dist (saddleCoordinates e s) (saddleCoordinates e mid) < r :=
    (dist_triangle _ (saddleCoordinates e (X 0)) _).trans_lt (by linarith)
  have hwr : dist (saddleCoordinates e w) (saddleCoordinates e mid) < r :=
    (dist_triangle _ (saddleCoordinates e (X 0)) _).trans_lt (by linarith)
  have hsB : s.B < (X 0).B := by
    have hh := congrFun hsc 0
    change s.B = (X 0).B+a*v 0 at hh
    have hneg := mul_neg_of_pos_of_neg ha hv0
    linarith
  have hwB : (X 0).B < w.B := by
    have hh := congrFun hwc 0
    change w.B = (X 0).B+b*((-1)*v 0) at hh
    have hpos := mul_pos hb (neg_pos.mpr hv0)
    nlinarith
  have hYq : pairConeValue e mid.z α X Y 0 < 0 := by
    simpa only [pairConeValue,hY0] using hwq
  have hZq : pairConeValue e mid.z α X Z 0 < 0 := by
    simpa only [pairConeValue,hZ0] using hsq
  have hYs := (hselect r hr hrd X Y hX hY hstayθ (by simpa only [hY0] using hwr) hYq).2
    (by simpa only [hY0] using hwB)
  have hZs := (hselect r hr hrd X Z hX hZ hstayθ (by simpa only [hZ0] using hsr) hZq).1
    (by simpa only [hZ0] using hsB)
  exact ⟨Y,Z,hY,hZ,by simpa only [hY0] using hwε,by simpa only [hZ0] using hsε,hYs,hZs⟩

end CoreCouplingGlobal

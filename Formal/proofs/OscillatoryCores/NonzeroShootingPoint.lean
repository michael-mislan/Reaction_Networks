import proofs.OscillatoryCores.LiteralShootingBranch
import proofs.OscillatoryCores.PeriodicFlowTransport

namespace OscillatoryCores

open Set Filter
open scoped Topology Matrix

theorem exists_positive_of_eventually {P : ℝ → Prop} (h : ∀ᶠ r in 𝓝 (0 : ℝ), P r) :
    ∃ r, 0 < r ∧ P r := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε/2,by positivity,hball ?_⟩
  simp only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
  rw [abs_of_pos (by positivity : 0 < ε/2)]
  linarith

/-- Select nonzero amplitude while preserving all trajectory constraints
uniformly for the entire unit-time return segment. -/
theorem literal_nonzero_shooting_point :
    ∃ t r P R : ℝ, ∃ x : ShootingState,
    ∃ g : ShootingState → ShootingState, ∃ Φ : ℝ → ShootingState → ShootingState,
      0 < t ∧ 0 < r ∧ 0 < P ∧
      x.1=t ∧ x.2.1=r ∧ x.2.2.1=P ∧
      (∀ y ∈ Metric.closedBall (0 : ShootingState) R, g y=augmentedField y) ∧
      (∀ y, Φ 0 y=y) ∧
      (∀ y s, HasDerivAt (fun s => Φ s y) (g (Φ s y)) s) ∧
      (∀ s p y, Φ s (Φ p y)=Φ (p+s) y) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Φ s x ∈ Metric.ball 0 R) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ i : Fin 4, 0 < 1+r*(Φ s x).2.2.2 i) ∧
      (Φ 1 x).2.2.2=x.2.2.2 ∧ amplitudeField t r x.2.2.2 ≠ 0 := by
  obtain ⟨t,T,R,u,e,f,g,Φ,z,ht,hT,hR,hu,hge,hΦ0,hΦ,hadd,hjoint,hz0,hzc,hres,hball,hvel⟩ :=
    literal_shooting_zero_branch
  let I := fun r => shootingInitial u e f r (z r)
  have hz00 : z 0 0=t := by simp [hz0]
  have hz01 : z 0 1=T := by simp [hz0]
  have hi0 : I 0=(t,0,T,u t) := by simp [I,shootingInitial,hz0]
  have hzcoord (i : Fin 4) : ContinuousAt (fun r => z r i) 0 := (continuous_apply i).continuousAt.comp hzc
  have hui : ContinuousAt (fun r => u (z r 0)) 0 := by
    have hu' : ContinuousAt u (z 0 0) := by simpa [hz00] using hu
    simpa only [Function.comp_def] using hu'.tendsto.comp (hzcoord 0).tendsto
  have hi : ContinuousAt I 0 :=
    (hzcoord 0).prodMk (continuousAt_id.prodMk ((hzcoord 1).prodMk
      ((hui.add ((hzcoord 2).smul continuousAt_const)).add ((hzcoord 3).smul continuousAt_const))))
  have hyc (s : ℝ) : ContinuousAt (fun p : ℝ × ℝ => Φ p.2 (I p.1)) (0,s) := by
    have hip : ContinuousAt (fun p : ℝ × ℝ => I p.1) (0,s) := by
      exact hi.tendsto.comp (continuous_fst.continuousAt.tendsto :
        Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (0,s)) (𝓝 (0 : ℝ)))
    exact hjoint.continuousAt.comp (continuousAt_snd.prodMk hip)
  have hbt : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, Φ s (I r) ∈ Metric.ball 0 R :=
    eventually_unit_curve_in_ball (fun r s => Φ s (I r)) 0 0 R (fun s _ => hyc s) hball
  have hpos : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ s ∈ Icc (0 : ℝ) 1, ∀ i : Fin 4,
      0 < 1+r*(Φ s (I r)).2.2.2 i := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s _
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun p : ℝ × ℝ => (1 : ℝ)+p.1*(Φ p.2 (I p.1)).2.2.2 i) (0,s) :=
      continuousAt_const.add (continuousAt_fst.mul
        ((continuous_apply i).continuousAt.comp (hyc s).snd.snd.snd))
    exact hc.eventually (isOpen_Ioi.mem_nhds (by simp))
  have htn : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < z r 0 :=
    (hzcoord 0).eventually (isOpen_Ioi.mem_nhds (by simpa [hz00] using ht))
  have hPn : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < z r 1 :=
    (hzcoord 1).eventually (isOpen_Ioi.mem_nhds (by simpa [hz01] using hT))
  have hgc : ContinuousAt (fun r => amplitudeField (z r 0) r (I r).2.2.2) 0 :=
    amplitudeField_contDiff.continuous.continuousAt.comp
      ((hzcoord 0).prodMk (continuousAt_id.prodMk hi.snd.snd.snd))
  have hgn : ∀ᶠ r in 𝓝 (0 : ℝ), amplitudeField (z r 0) r (I r).2.2.2 ≠ 0 :=
    hgc.eventually_ne (by simpa only [hz00,hi0] using hvel)
  have hall : ∀ᶠ r in 𝓝 (0 : ℝ),
      0 < z r 0 ∧ 0 < z r 1 ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Φ s (I r) ∈ Metric.ball 0 R) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ i : Fin 4, 0 < 1+r*(Φ s (I r)).2.2.2 i) ∧
      (Φ 1 (I r)).2.2.2=(I r).2.2.2 ∧ amplitudeField (z r 0) r (I r).2.2.2 ≠ 0 := by
    filter_upwards [htn,hPn,hbt,hpos,hres,hgn] with r hr hP hB hpos hres hgn
    exact ⟨hr,hP,hB,hpos,sub_eq_zero.mp hres,hgn⟩
  obtain ⟨r,hr,hrt,hrP,hrB,hrpos,hrret,hrvel⟩ := exists_positive_of_eventually hall
  exact ⟨z r 0,r,z r 1,R,I r,g,Φ,hrt,hr,hrP,rfl,rfl,rfl,hge,hΦ0,hΦ,hadd,hrB,hrpos,hrret,hrvel⟩

end OscillatoryCores

import proofs.OscillatoryCores.NonzeroShootingPoint

namespace OscillatoryCores

open Set

/-- A nonzero-amplitude, positive, nonstationary periodic solution of the
exact polynomial amplitude equation. -/
theorem amplitude_periodic_orbit :
    ∃ t r P : ℝ, ∃ y : ℝ → State,
      0 < t ∧ 0 < r ∧ 0 < P ∧ Function.Periodic y 1 ∧
      (∀ s, HasDerivAt y (P • amplitudeField t r (y s)) s) ∧
      (∀ s i, 0 < 1+r*y s i) ∧ amplitudeField t r (y 0) ≠ 0 := by
  obtain ⟨t,r,P,R,x,g,Φ,ht,hr,hP,hxt,hxr,hxP,hge,hΦ0,hΦ,hadd,hball,hpos,hret,hvel⟩ :=
    literal_nonzero_shooting_point
  have hclosed : ∀ s ∈ Icc (0 : ℝ) 1, Φ s x ∈ Metric.closedBall 0 R :=
    fun s hs => Metric.ball_subset_closedBall (hball s hs)
  have hfull := full_return_of_displacement_return g Φ hΦ0 hΦ 0 R hge x hclosed hret
  have hperiodic := flow_periodic_of_return Φ hadd x hfull
  have hballall : ∀ s, Φ s x ∈ Metric.closedBall 0 R :=
    periodic_unit_property (fun s => Φ s x) hperiodic _ hclosed
  have hstatic : ∀ s, staticCoordinates (Φ s x)=staticCoordinates x :=
    periodic_unit_property (fun s => Φ s x) hperiodic (fun p => staticCoordinates p=staticCoordinates x)
      (unit_static_coordinates g Φ hΦ0 hΦ 0 R hge x hclosed)
  let y := fun s => (Φ s x).2.2.2
  refine ⟨t,r,P,y,ht,hr,hP,?_,?_,?_,?_⟩
  · intro s
    exact congrArg (fun x : ShootingState => x.2.2.2) (hperiodic s)
  · intro s
    have hd := (hΦ x s).snd.snd.snd
    have hs := hstatic s
    have hs1 : (Φ s x).1=t := (congrArg (fun p : ℝ × ℝ × ℝ => p.1) hs).trans hxt
    have hs2 : (Φ s x).2.1=r := (congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hs).trans hxr
    have hs3 : (Φ s x).2.2.1=P := (congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hs).trans hxP
    simpa only [hge _ (hballall s),augmentedField,hs1,hs2,hs3,y] using hd
  · exact periodic_unit_property (fun s => Φ s x) hperiodic
      (fun q => ∀ i : Fin 4, 0 < 1+r*q.2.2.2 i) hpos
  · simpa only [y,hΦ0] using hvel

end OscillatoryCores

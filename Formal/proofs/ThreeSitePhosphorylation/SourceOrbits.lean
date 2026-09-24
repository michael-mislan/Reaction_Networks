import proofs.ThreeSitePhosphorylation.FamilyBounds
import proofs.ThreeSitePhosphorylation.GlobalOrbit

namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

def sourceOrbitProperty (ε : ℝ) (y : State) : Prop :=
  (∀ i, 0<y i) ∧ ‖y-witnessState‖<ε ∧
    totalE y=totalE witnessState ∧ totalF y=totalF witnessState ∧ totalS y=totalS witnessState

theorem family_small_source_orbits {r w : ℝ} (C : ClosedPathFamily r w)
    (hr : 0<r) (hw : 0<w) (hp : candidatePolynomial r (Complex.I*(w:ℂ))=0)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a in 𝓝 (0:ℝ), a ≠ 0 →
      ∃ φ : ℝ → State, Function.Periodic φ (C.parameters a).2.im ∧
        (∀ s, HasDerivAt φ (field (witnessRates (C.parameters a).2.re) (φ s)) s) ∧
        (∀ s, sourceOrbitProperty ε (φ s)) ∧ ∃ s, φ s ≠ φ 0 := by
  filter_upwards [C.residual,C.closed,familyFullPath_positive C,familyFullPath_small C ε hε,
    family_velocity_nonzero C hw hp,family_parameters_near C hr hw ε hε]
    with a hres hclosed hpos hsmall hvel hparam
  intro ha
  let p := shootingArgument (a,C.parameters a)
  let u := pathContinuation p (C.paths a)
  let f : ℝ → State := fun t => chart (a • u t)
  have hu0 : u 0=(C.parameters a).1 := pathContinuation_initial p (C.paths a)
  have hu (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : u t=C.paths a ⟨t,ht⟩ :=
    (pathContinuation_eq p (C.paths a) hres ⟨t,ht⟩).symm
  have he : f 0=f 1 := by
    dsimp [f]
    rw [hu0,hu 1 (by norm_num),hclosed]
  have hf (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      HasDerivAt f ((C.parameters a).2.im • field (witnessRates (C.parameters a).2.re) (f t)) t :=
    lift_rescaled_derivative a (C.parameters a).2.re (C.parameters a).2.im t u
      (pathContinuation_solves p (C.paths a) hres t ht)
  have hP (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : sourceOrbitProperty ε (f t) := by
    dsimp [f,sourceOrbitProperty]
    rw [hu t ht]
    exact ⟨hpos ⟨t,ht⟩,hsmall ⟨t,ht⟩,chart_totals _⟩
  have hn : field (witnessRates (C.parameters a).2.re) (f 0) ≠ 0 := by
    intro hz
    have hl : liftOperator (a • rescaledField a (C.parameters a).2.re (C.parameters a).1)=0 := by
      rw [rescaledField_source,lift_reduced_field]
      simpa only [f,hu0] using hz
    have hzero : a • rescaledField a (C.parameters a).2.re (C.parameters a).1=0 := by
      apply tangent_injective
      simpa only [map_zero] using hl
    exact hvel ((smul_eq_zero.mp hzero).resolve_left ha)
  exact globalize_closed_source (C.parameters a).2.re (C.parameters a).2.im hparam.2.1 f
    (sourceOrbitProperty ε) he hf hP hn

end
end ThreeSitePhosphorylation

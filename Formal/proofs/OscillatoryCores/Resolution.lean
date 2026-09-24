import proofs.OscillatoryCores.PeriodicOrbit
import proofs.OscillatoryCores.ChildSafety

namespace OscillatoryCores

open DUnstableCores

/-- The fixed four-species, five-reaction source with orders p=400 and
q=375 is a literal positive mass-action oscillator, has no supported
D-unstable child, and loses all nonconstant positive periodic trajectories
after any proper reaction deletion, even with arbitrary nonnegative retuning. -/
theorem literal_oscillator_resolution :
    (∃ k : Fin 5 → ℝ, ∃ x : ℝ → State, ∃ P : ℝ,
      (∀ j, 0 < k j) ∧ 0 < P ∧ (∀ s i, 0 < x s i) ∧
      Solves k x ∧ Function.Periodic x P ∧ (∃ s, x s ≠ x 0)) ∧
    (∀ κ : ChildSelection source, DNonUnstable κ.realMatrix) ∧
    (∀ k : Fin 5 → ℝ, (∀ j, 0 ≤ k j) →
      ∀ j0 : Fin 5, k j0=0 →
      ∀ x : ℝ → State, (∀ s i, 0 < x s i) → Solves k x →
      ∀ P : ℝ, 0 < P → Function.Periodic x P → ∀ s, x s=x 0) := by
  refine ⟨literal_positive_periodic_orbit,all_children_dNonUnstable,?_⟩
  intro k hk j0 hj0 x hpos hode P hP hperiod
  have hreturn : x P=x 0 := by simpa using hperiod 0
  exact proper_deletion_returning_trajectory_constant k hk j0 hj0 x hpos hode P hP hreturn

theorem literal_no_dUnstableCore :
    ¬ ∃ κ : ChildSelection source, IsDUnstableCore κ := by
  rintro ⟨κ,hκ⟩
  obtain ⟨d,hd,hunstable⟩ := hκ.1
  exact all_children_dNonUnstable κ d hd hunstable

end OscillatoryCores

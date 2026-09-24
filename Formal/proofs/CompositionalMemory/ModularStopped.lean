import proofs.CompositionalMemory.CoupledCounts
import proofs.FiniteCopy.UniformizedBounds
import proofs.HeritableCompositions.AffineRecovery

namespace CompositionalMemory
open FiniteCopy

abbrev StoppedModularState {k : ℕ} (D : Finset (ModularCountState k)) :=
  Option {s : ModularCountState k // s ∈ D}

/-- Kill on the first departure from the chosen finite pre-division domain. -/
noncomputable def killedModularModel {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (D : Finset (ModularCountState k)) :
    FiniteJumpModel (StoppedModularState D) (ModularChannel k) := by
  classical
  exact {
    next := fun s r => match s with
      | none => none
      | some s => if h : modularNext s.val r ∈ D then some ⟨modularNext s.val r,h⟩ else none
    rate := fun s r => match s with
      | none => 0
      | some s => modularRate γ w s.val r
    nonneg := by
      intro s r
      cases s with
      | none => rfl
      | some s => exact modular_rate_nonnegative γ w hγ hw s.val r }

noncomputable def stoppedModularObservable {k : ℕ} (D : Finset (ModularCountState k))
    (f : ModularCountState k → ℝ) (boundary : ℝ) : StoppedModularState D → ℝ
  | none => boundary
  | some s => f s.val

theorem killed_modular_generator_le {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (D : Finset (ModularCountState k))
    (f : ModularCountState k → ℝ) (boundary : ℝ)
    (hb : ∀ s ∈ D, ∀ r, modularNext s r ∉ D → boundary ≤ f (modularNext s r))
    (s : {s : ModularCountState k // s ∈ D}) :
    (killedModularModel γ w hγ hw D).generator (stoppedModularObservable D f boundary) (some s) ≤
      modularGenerator γ w f s.val := by
  classical
  unfold FiniteJumpModel.generator modularGenerator
  apply Finset.sum_le_sum
  intro r _
  have hh : stoppedModularObservable D f boundary
      ((killedModularModel γ w hγ hw D).next (some s) r) ≤ f (modularNext s.val r) := by
    by_cases hd : modularNext s.val r ∈ D
    · simp [killedModularModel,stoppedModularObservable,hd]
    · simpa [killedModularModel,stoppedModularObservable,hd] using hb s.val s.property r hd
  simpa [killedModularModel,stoppedModularObservable] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hh (f s.val))
      (modular_rate_nonnegative γ w hγ hw s.val r)

/-- Zero at the cemetery preserves affine recovery; freezing a high exit value
would not justify this conclusion. -/
theorem killed_modular_affine {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (D : Finset (ModularCountState k))
    (f : ModularCountState k → ℝ) (decay C : ℝ)
    (hf : ∀ s, 0 ≤ f s) (hd : 0 ≤ decay) (hC : 0 ≤ C)
    (hgen : ∀ s ∈ D, modularGenerator γ w f s ≤ -decay*f s+decay*C)
    (s : StoppedModularState D) :
    (killedModularModel γ w hγ hw D).generator (stoppedModularObservable D f 0) s ≤
      -decay*stoppedModularObservable D f 0 s+decay*C := by
  cases s with
  | none =>
    simpa [killedModularModel,FiniteJumpModel.generator,stoppedModularObservable] using mul_nonneg hd hC
  | some s =>
    exact (killed_modular_generator_le γ w hγ hw D f 0 (fun t _ r _ => hf (modularNext t r)) s).trans
      (hgen s.val s.property)

end CompositionalMemory

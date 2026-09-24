import proofs.CompositionalMemory.RetainedModular

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def modularActiveObservable (N : ℕ) (D : Finset (ModularCountState k)) (f : ModularCountState k → ℝ) :
    StoppedModularState D → ℝ
  | none => 0
  | some c => if c.val.2 < 2*(k*N) then f c.val else 0

theorem modularActiveObservable_nonneg (N : ℕ) (D : Finset (ModularCountState k)) (f : ModularCountState k → ℝ)
    (hf : ∀ c, 0 ≤ f c) (c : StoppedModularState D) : 0 ≤ modularActiveObservable N D f c := by
  cases c with
  | none => exact le_rfl
  | some c => dsimp [modularActiveObservable]; split_ifs <;> first | exact hf c.val | exact le_rfl

theorem modular_active_generator_le {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (D : Finset (ModularCountState k))
    (f : ModularCountState k → ℝ) (hf : ∀ c, 0 ≤ f c) (c : {c : ModularCountState k // c ∈ D})
    (hc : c.val.2 < 2*(k*N)) :
    (retainedModularModel γ w hγ hw N D).generator (modularActiveObservable N D f) (some c) ≤
      modularGenerator γ w f c.val := by
  classical
  unfold FiniteJumpModel.generator modularGenerator
  apply Finset.sum_le_sum
  intro r _
  have hn : modularActiveObservable N D f ((retainedModularModel γ w hγ hw N D).next (some c) r) ≤
      f (modularNext c.val r) := by
    by_cases hd : modularNext c.val r ∈ D
    · by_cases ha : (modularNext c.val r).2 < 2*(k*N)
      · simp [retainedModularModel,hc,hd,modularActiveObservable,ha]
      · simpa [retainedModularModel,hc,hd,modularActiveObservable,ha] using hf (modularNext c.val r)
    · simpa [retainedModularModel,hc,hd,modularActiveObservable] using hf (modularNext c.val r)
  simpa [retainedModularModel,hc,modularActiveObservable] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hn (f c.val)) (modular_rate_nonnegative γ w hγ hw c.val r)

theorem modular_retained_affine_event {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (hw : ∀ i j, 0 ≤ w i j) (hγ : 0 ≤ γ) (N : ℕ) (D : Finset (ModularCountState k))
    (f : ModularCountState k → ℝ) (hf : ∀ c, 0 ≤ f c) (decay C : ℝ) (hk0 : 0 ≤ decay) (hC : 0 ≤ C)
    (hgen : ∀ c ∈ D, c.2 < 2*(k*N) → modularGenerator γ w f c ≤ -decay*f c+decay*C)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ c, (retainedModularModel γ w hγ hw N D).total c ≤ q) (hk : decay ≤ q)
    (A : Set (StoppedModularState D)) (a : ℝ)
    (hA : ∀ c ∈ A, a ≤ modularActiveObservable N D f c)
    (c : {c : ModularCountState k // c ∈ D}) (hc : c.val.2 < 2*(k*N)) :
    a*((retainedModularModel γ w hγ hw N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some c) ≤ Real.exp (-decay*(t : ℝ))*f c.val+C := by
  have hp : 0 ≤ decay*C := mul_nonneg hk0 hC
  have hG : ∀ x, (retainedModularModel γ w hγ hw N D).generator (modularActiveObservable N D f) x ≤
      -decay*modularActiveObservable N D f x+decay*C := by
    intro x
    cases x with
    | none => simpa [retainedModularModel,FiniteJumpModel.generator,modularActiveObservable] using hp
    | some x =>
      by_cases hx : x.val.2 < 2*(k*N)
      · have h := (modular_active_generator_le γ w hw hγ N D f hf x hx).trans (hgen x.val x.property hx)
        simpa only [modularActiveObservable,if_pos hx] using h
      · simpa [retainedModularModel,FiniteJumpModel.generator,hx,modularActiveObservable] using hp
  have h := uniformized_event_affine (retainedModularModel γ w hγ hw N D) q t hq hclock
    A (modularActiveObservable N D f) a decay C (modularActiveObservable_nonneg N D f hf) hA hk hC hG (some c)
  simpa only [modularActiveObservable,if_pos hc] using h

end CompositionalMemory

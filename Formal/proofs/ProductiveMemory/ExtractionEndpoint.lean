import proofs.ProductiveMemory.ExtractionWell
import proofs.HeritableCompositions.AffineRecovery

namespace ProductiveMemory
open FiniteCopy HeritableCompositions Set
open scoped NNReal
noncomputable section
set_option Elab.async false

theorem extraction_affine_event (rho : ℝ) (hr : 0 ≤ rho) (N : ℕ) (D : Finset Counts)
    (f : Point → ℝ) (hf : ∀ x, 0 ≤ f x) (k C : ℝ) (hk0 : 0 ≤ k) (hC : 0 ≤ C)
    (hgen : ∀ n ∈ D, countGenerator rho N f (concentration N n) ≤
      -k*f (concentration N n)+k*C)
    (q t : NNReal) (hq : 0 < (q:ℝ))
    (hclock : ∀ s, (extractionStoppedModel rho hr N D).total s ≤ q) (hk : k ≤ q)
    (A : Set (ExtractionStoppedCounts D)) (a : ℝ)
    (hA : ∀ s ∈ A, a ≤ extractionStoppedObservable N D f 0 s)
    (n : {n : Counts // n ∈ D}) :
    a*((extractionStoppedModel rho hr N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator A) (some n) ≤ Real.exp (-k*(t:ℝ))*f (concentration N n.val)+C := by
  classical
  apply uniformized_event_affine (extractionStoppedModel rho hr N D) q t hq hclock
    A (extractionStoppedObservable N D f 0) a k C
  · intro x
    cases x with
    | none => exact le_rfl
    | some x => exact hf _
  · exact hA
  · exact hk
  · exact hC
  · intro x
    cases x with
    | none => simpa [extractionStoppedModel,FiniteJumpModel.generator,extractionStoppedObservable] using mul_nonneg hk0 hC
    | some x =>
      exact (extraction_stopped_generator_le rho hr N D f 0
        (fun _ _ _ _ _ => hf _) x).trans (hgen x.val x.property)

def terminalUnready (N : ℕ) (D : Finset Counts) (s : Point) (E : Point → ℝ) :
    Set (ExtractionStoppedCounts D) :=
  {n | match n with
    | none => False
    | some n => readyLevel < E (fun i => concentration N n.val i-s i)}

theorem terminal_exponential_tail (u p W : ℝ) (hu : 0 ≤ u)
    (hW : W ≤ Real.exp (8*u))
    (hbound : Real.exp u*p ≤ Real.exp (-(56/5)*u)*W+2*Real.exp (u/2)) :
    p ≤ Real.exp (-u)+2*Real.exp (-u/2) := by
  have hex : Real.exp (-(56/5)*u) ≤ Real.exp (-8*u) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpos := (Real.exp_pos (8*u)).le
  have hm := mul_le_mul hW hex (Real.exp_pos _).le hpos
  have he : Real.exp (8*u)*Real.exp (-8*u) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [he] at hm
  have hid : Real.exp u*(Real.exp (-u)+2*Real.exp (-u/2)) = 1+2*Real.exp (u/2) := by
    rw [mul_add,mul_left_comm (Real.exp u) 2,← Real.exp_add,← Real.exp_add]
    have h1 : u + -u = 0 := by ring
    have h2 : u + -u/2 = u/2 := by ring
    rw [h1,h2,Real.exp_zero]
  have hb : Real.exp u*p ≤ Real.exp u*(Real.exp (-u)+2*Real.exp (-u/2)) := by
    rw [hid]
    nlinarith only [hbound,hm]
  exact (mul_le_mul_iff_right₀ (Real.exp_pos u)).mp hb

end
end ProductiveMemory

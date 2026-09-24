import proofs.ProductiveMemory.ExtractionStopped

namespace ProductiveMemory
open FiniteCopy
set_option Elab.async false
open scoped NNReal

/-- Killing on departure gives zero boundary value. This differs from keeping
the exit value of the observable, which does not imply exponential decay. -/
theorem extraction_killed_survival_bound (e : ℝ) (he : 0 ≤ e) (N : ℕ)
    (D : Finset Counts) (f : Point → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hone : ∀ n ∈ D, 1 ≤ f (concentration N n)) (k : ℝ)
    (hgen : ∀ n ∈ D, countGenerator e N f (concentration N n) ≤
      -k*f (concentration N n))
    (q t : ℝ≥0) (hq : 0 < (q : ℝ)) (hkq : k ≤ q)
    (hclock : ∀ s, (extractionStoppedModel e he N D).total s ≤ q)
    (n : {n : Counts // n ∈ D}) :
    ((extractionStoppedModel e he N D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {s | s ≠ none}) (some n) ≤
        Real.exp (-k*(t : ℝ))*f (concentration N n.val) := by
  classical
  let M := extractionStoppedModel e he N D
  let P := M.uniformize q hq hclock
  let W := extractionStoppedObservable N D f 0
  have hG (s) : M.generator W s ≤ -k*W s := by
    cases s with
    | none => simp [M, W, extractionStoppedObservable, extraction_stopped_none_generator]
    | some m => exact (extraction_stopped_generator_le e he N D f 0
        (fun _ _ _ _ _ => hf _) m).trans (hgen m.val m.property)
  have hI (s) : FiniteKernel.eventIndicator {s | s ≠ none} s ≤ W s := by
    cases s with
    | none => simp [FiniteKernel.eventIndicator, W, extractionStoppedObservable]
    | some m => simpa [FiniteKernel.eventIndicator, W, extractionStoppedObservable] using hone m.val m.property
  let r : ℝ := 1-k/(q : ℝ)
  have hr : 0 ≤ r := sub_nonneg.mpr ((div_le_one hq).mpr hkq)
  have hstep := M.uniformize_decay q hq hclock W k hG
  have hsR : HasSum (fun j => poissonWeight (q*t) j*(r^j*W (some n)))
      (Real.exp (((q*t : ℝ≥0) : ℝ)*(r-1))*W (some n)) := by
    convert (poissonWeight_geometric (q*t) r).mul_right (W (some n)) using 1
    funext j; ring
  have hm (j) : poissonWeight (q*t) j*P.steps j
      (FiniteKernel.eventIndicator {s | s ≠ none}) (some n) ≤
      poissonWeight (q*t) j*(r^j*W (some n)) :=
    mul_le_mul_of_nonneg_left ((P.steps_mono hI j (some n)).trans
      (P.steps_decay_bound W r hr hstep j (some n))) (poissonWeight_nonneg _ _)
  have h := (Summable.tsum_le_tsum hm (P.event_summable (q*t) _ (some n))
    hsR.summable).trans_eq hsR.tsum_eq
  have heq : ((q*t : ℝ≥0) : ℝ)*(r-1) = -k*(t : ℝ) := by
    dsimp [r]
    field_simp
    ring
  simpa only [heq] using h

end ProductiveMemory


import proofs.CompositionalMemory.CountCutoff
import proofs.CompositionalMemory.ModularStopped
import proofs.FiniteCopy.KernelExpectations

namespace CompositionalMemory
open FiniteCopy

theorem count_cutoff_generator {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (R : ℕ) (s : StoppedModularState (countCutoff k R)) :
    (killedModularModel γ w hγ hw (countCutoff k R)).generator
      (stoppedModularObservable (countCutoff k R) globalMoleculeCount R) s ≤
        33*stoppedModularObservable (countCutoff k R) globalMoleculeCount R s := by
  cases s with
  | none => simp [killedModularModel,FiniteJumpModel.generator,stoppedModularObservable]
  | some s =>
    exact (killed_modular_generator_le γ w hγ hw (countCutoff k R)
      globalMoleculeCount R (count_cutoff_departure R) s).trans
        (global_count_growth hk γ w s.val ((mem_countCutoff R s.val).mp s.property).1)

/-- A bound for the actual first departure of each finite total-count cutoff.
The time variable is the source's rescaled time tau=t/k. -/
theorem count_cutoff_exit_bound {k : ℕ} (hk : 1 ≤ k) (γ : ℝ)
    (w : Fin k → Fin k → ℝ) (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j)
    (R : ℕ) (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (killedModularModel γ w hγ hw (countCutoff k R)).total s ≤ q)
    (s : {s : ModularCountState k // s ∈ countCutoff k R}) :
    (R : ℝ)*((killedModularModel γ w hγ hw (countCutoff k R)).uniformize q hq hclock).poissonized
      (q*t) (FiniteKernel.eventIndicator {none}) (some s) ≤
        Real.exp (33*(t : ℝ))*globalMoleculeCount s.val := by
  classical
  let D := countCutoff k R
  let M := killedModularModel γ w hγ hw D
  let W := stoppedModularObservable D globalMoleculeCount (R : ℝ)
  have hW (x) : 0 ≤ W x := by
    cases x with
    | none => exact Nat.cast_nonneg R
    | some x => exact global_count_nonneg x.val
  have hg (x) : M.generator W x ≤ -(-33)*W x := by
    simpa only [neg_neg] using count_cutoff_generator hk γ w hγ hw R x
  have hdec := M.uniformized_decay_bound q t hq hclock W hW (-33)
    ((by norm_num : (-33 : ℝ) ≤ 0).trans q.property) hg (some s)
  have hI (x) : (R : ℝ)*FiniteKernel.eventIndicator {none} x ≤ W x := by
    cases x with
    | none => simp [FiniteKernel.eventIndicator,W,stoppedModularObservable]
    | some x => simpa [FiniteKernel.eventIndicator,W,stoppedModularObservable] using global_count_nonneg x.val
  have hm := (M.uniformize q hq hclock).poissonized_mono (q*t)
    (fun x => (R : ℝ)*FiniteKernel.eventIndicator {none} x) W
    (fun x => mul_nonneg (Nat.cast_nonneg R) (by unfold FiniteKernel.eventIndicator; positivity))
    hW hI (some s)
  rw [FiniteKernel.poissonized_scale] at hm
  exact hm.trans (by simpa only [neg_neg] using hdec)

end CompositionalMemory

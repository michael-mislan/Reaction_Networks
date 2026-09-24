import proofs.CompositionalMemory.GenericEarlyClock
import proofs.CompositionalMemory.GenericRetainedRecovery
import proofs.HeritableCompositions.KernelComposition

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

noncomputable def generalFirstBad {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d))
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (recover : ℝ) :
    Set (Option {s : GeneralCountState k d // s ∈ D}) :=
  {x | match x with | none => True | some s => ¬(s.val.2 < 2*(k*N) ∧
    ∀ i, E i (fun a => generalConcentration s.val i a-center i a) ≤ recover)}

noncomputable def generalUnrecovered {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d))
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (recover : ℝ) :
    Set (Option {s : GeneralCountState k d // s ∈ D}) :=
  {x | match x with | none => False | some s => s.val.2 < 2*(k*N) ∧
    ∃ i, recover < E i (fun a => generalConcentration s.val i a-center i a)}

theorem general_first_bad_covered {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d))
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (recover : ℝ)
    (x : Option {s : GeneralCountState k d // s ∈ D}) :
    FiniteKernel.eventIndicator (generalFirstBad N D center E recover) x ≤
      FiniteKernel.eventIndicator {none} x+
      (FiniteKernel.eventIndicator (generalDivisionRecorded N D) x+
       FiniteKernel.eventIndicator (generalUnrecovered N D center E recover) x) := by
  classical
  cases x with
  | none => simp [FiniteKernel.eventIndicator,generalFirstBad,generalDivisionRecorded,generalUnrecovered]
  | some s =>
    by_cases ha : s.val.2 < 2*(k*N)
    · have hdiv : ¬2*(k*N) ≤ s.val.2 := not_le.mpr ha
      by_cases he : ∀ i, E i (fun a => generalConcentration s.val i a-center i a) ≤ recover
      · have hn : ¬∃ i, recover < E i (fun a => generalConcentration s.val i a-center i a) := by
          simp only [not_exists]
          intro i
          exact not_lt.mpr (he i)
        simp [FiniteKernel.eventIndicator,generalFirstBad,generalDivisionRecorded,generalUnrecovered,ha,hdiv,hn]
      · have hn := he
        push Not at hn
        simp [FiniteKernel.eventIndicator,generalFirstBad,generalDivisionRecorded,generalUnrecovered,ha,hdiv,hn]
    · have hdiv : 2*(k*N) ≤ s.val.2 := Nat.le_of_not_gt ha
      simp [FiniteKernel.eventIndicator,generalFirstBad,generalDivisionRecorded,generalUnrecovered,ha,hdiv]

theorem general_unrecovered_exponential_covered {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d))
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (recover α : ℝ) (hα : 0 ≤ α)
    (x : Option {s : GeneralCountState k d // s ∈ D}) :
    FiniteKernel.eventIndicator (generalUnrecovered N D center E recover) x ≤
      FiniteKernel.eventIndicator {x | ∃ i, Real.exp (α*(N:ℝ)*recover) ≤
        retainedActiveObservable (fun s => s.2 < 2*(k*N)) D
          (fun s => Real.exp (α*(N:ℝ)*E i (fun a => generalConcentration s i a-center i a))) x} x := by
  classical
  by_cases hx : x ∈ generalUnrecovered N D center E recover
  · have ht : ∃ i, Real.exp (α*(N:ℝ)*recover) ≤
        retainedActiveObservable (fun s => s.2 < 2*(k*N)) D
          (fun s => Real.exp (α*(N:ℝ)*E i (fun a => generalConcentration s i a-center i a))) x := by
      cases x with
      | none => exact False.elim hx
      | some s =>
        obtain ⟨ha,i,hi⟩ := hx
        refine ⟨i,?_⟩
        simp only [retainedActiveObservable,retainedReactionObservable,if_pos ha]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi.le (mul_nonneg hα (Nat.cast_nonneg N)))
    simp only [FiniteKernel.eventIndicator,if_pos hx,Set.mem_setOf_eq,if_pos ht,le_refl]
  · simp only [FiniteKernel.eventIndicator,if_neg hx]
    split_ifs <;> norm_num

theorem general_first_phase_event_bound {k d : ℕ} (N : ℕ) (D : Finset (GeneralCountState k d))
    (center : Fin k → Fin d → ℝ) (E : Fin k → (Fin d → ℝ) → ℝ) (recover α : ℝ) (hα : 0 ≤ α)
    (P : FiniteKernel (Option {s : GeneralCountState k d // s ∈ D})) (t : NNReal)
    (x : Option {s : GeneralCountState k d // s ∈ D}) :
    P.poissonized t (FiniteKernel.eventIndicator (generalFirstBad N D center E recover)) x ≤
      P.poissonized t (FiniteKernel.eventIndicator {none}) x+
      (P.poissonized t (FiniteKernel.eventIndicator (generalDivisionRecorded N D)) x+
       P.poissonized t (FiniteKernel.eventIndicator {x | ∃ i, Real.exp (α*(N:ℝ)*recover) ≤
        retainedActiveObservable (fun s => s.2 < 2*(k*N)) D
          (fun s => Real.exp (α*(N:ℝ)*E i (fun a => generalConcentration s i a-center i a))) x}) x) := by
  have h := poisson_mono P t _ _ (general_first_bad_covered N D center E recover) x
  rw [poisson_additive,poisson_additive] at h
  exact h.trans (add_le_add le_rfl (add_le_add le_rfl
    (poisson_mono P t _ _ (general_unrecovered_exponential_covered N D center E recover α hα) x)))

end CompositionalMemory

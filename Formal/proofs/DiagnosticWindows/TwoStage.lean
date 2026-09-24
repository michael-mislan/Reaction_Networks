import proofs.FiniteCopy.PoissonKernel

namespace DiagnosticWindows
open FiniteCopy
open scoped BigOperators

/-- Uniformization at rate one of the aggregate source 0 -> 1 -> 2.
State 2 is the irreversible positive-call latch. Both hypotheses use this kernel. -/
noncomputable def source (p q : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) : FiniteKernel (Fin 3) where
  prob := ![![1-p,p,0], ![0,1-q,q], ![0,0,1]]
  nonneg := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp <;> linarith [hp.1,hp.2,hq.1,hq.2]
  row_sum := by
    intro x
    fin_cases x <;> simp [Fin.sum_univ_succ]

def negative : Fin 3 → ℝ := ![1,1,0]

theorem source_steps (p q : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hne : q-p ≠ 0) (n : ℕ) :
    (source p q hp hq).steps n negative =
      ![(q*(1-p)^n-p*(1-q)^n)/(q-p), (1-q)^n, 0] := by
  induction n with
  | zero =>
    funext x
    fin_cases x <;> simp [FiniteKernel.steps,negative, hne]
  | succ n ih =>
    funext x
    change (source p q hp hq).step ((source p q hp hq).steps n negative) x = _
    rw [ih]
    fin_cases x <;> simp [FiniteKernel.step,source,Fin.sum_univ_succ,pow_succ]
    all_goals field_simp
    all_goals ring

/-- Exact survival probability of the actual Poissonized finite kernel.
This is derived from the source, not supplied as a tail assumption. -/
theorem source_survival (p q : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hne : q-p ≠ 0) (t : NNReal) :
    (source p q hp hq).poissonized t negative 0 =
      (q*Real.exp (-(p*(t:ℝ)))-p*Real.exp (-(q*(t:ℝ))))/(q-p) := by
  have hs := (((poissonWeight_geometric t (1-p)).mul_left q).sub
    ((poissonWeight_geometric t (1-q)).mul_left p)).div_const (q-p)
  have he : (fun n => poissonWeight t n * (source p q hp hq).steps n negative 0) =
      (fun n => (q*(poissonWeight t n*(1-p)^n)-
        p*(poissonWeight t n*(1-q)^n))/(q-p)) := by
    funext n
    rw [source_steps p q hp hq hne]
    simp only [Matrix.cons_val_zero]
    ring
  unfold FiniteKernel.poissonized
  rw [he,hs.tsum_eq]
  rw [show (t:ℝ)*(1-p-1) = -(p*(t:ℝ)) by ring,
    show (t:ℝ)*(1-q-1) = -(q*(t:ℝ)) by ring]

theorem source_survival_one (p q : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hne : q-p ≠ 0) (t : NNReal) :
    (source p q hp hq).poissonized t negative 1 = Real.exp (-(q*(t:ℝ))) := by
  unfold FiniteKernel.poissonized
  simp_rw [source_steps p q hp hq hne]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]
  rw [(poissonWeight_geometric t (1-q)).tsum_eq]
  congr 1
  ring

theorem source_survival_two (p q : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hne : q-p ≠ 0) (t : NNReal) :
    (source p q hp hq).poissonized t negative 2 = 0 := by
  unfold FiniteKernel.poissonized
  simp_rw [source_steps p q hp hq hne]
  simp

end DiagnosticWindows

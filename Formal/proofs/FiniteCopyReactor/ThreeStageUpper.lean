import proofs.FiniteCopyReactor.MarkedUpper

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

def threeStage {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : ℝ≥0) (f : α → ℝ → ℝ) (x : α) (z : ℝ) : ℝ :=
  P.poissonized t (fun y a => Q.poissonized u (fun w b => R.poissonized v f w b) y a) x z

theorem three_stage_upper {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (t u v : ℝ≥0) (s rho K : ℝ) (hs : 0 ≤ s) (hrho : 0 ≤ rho)
    (hP : ∀ x z, P.step (fun _ w => Real.exp (s*w)) x z ≤ rho*Real.exp (s*z))
    (hQ : ∀ x z, Q.step (fun _ w => Real.exp (s*w)) x z ≤ rho*Real.exp (s*z))
    (hR : ∀ x z, R.step (fun _ w => Real.exp (s*w)) x z ≤ rho*Real.exp (s*z)) (x : α) (z : ℝ) :
    threeStage P Q R t u v (MarkedKernel.eventIndicator {a | K ≤ a.2}) x z ≤
      Real.exp (-s*K+((t:ℝ)+(u:ℝ)+(v:ℝ))*(rho-1)+s*z) := by
  let E := MarkedKernel.eventIndicator {a : α × ℝ | K ≤ a.2}
  have hb (y a) : 0 ≤ E y a ∧ E y a ≤ 1 := R.event_bounds _ 0 y a
  have hi (y a) : E y a ≤ Real.exp (-s*K)*Real.exp (s*a) := by
    unfold E MarkedKernel.eventIndicator
    split_ifs with h
    · rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hh := mul_le_mul_of_nonneg_left h hs
      linarith
    · positivity
  have hlast (y a) := marked_exponential_domination R E hb (Real.exp (-s*K)) s rho
    (Real.exp_pos _).le hrho hi hR v y a
  have hlastB (y a) := marked_bounded_poisson R E hb v y a
  have hmid (y a) := marked_exponential_domination Q (fun w b => R.poissonized v E w b)
    hlastB (Real.exp (-s*K)*Real.exp ((v:ℝ)*(rho-1))) s rho
    (by positivity) hrho hlast hQ u y a
  have hmidB (y a) := marked_bounded_poisson Q (fun w b => R.poissonized v E w b) hlastB u y a
  have hfirst := marked_exponential_domination P
    (fun y a => Q.poissonized u (fun w b => R.poissonized v E w b) y a) hmidB
    (Real.exp (-s*K)*Real.exp ((v:ℝ)*(rho-1))*Real.exp ((u:ℝ)*(rho-1))) s rho
    (by positivity) hrho hmid hP t x z
  apply hfirst.trans_eq
  rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

end
end FiniteCopyReactor

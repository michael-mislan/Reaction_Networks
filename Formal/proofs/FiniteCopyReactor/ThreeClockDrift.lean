import proofs.FiniteCopy.KernelExpectations

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical
open scoped NNReal

theorem finite_two_clock_drift {α : Type*} [Fintype α] (P Q : FiniteKernel α)
    (t u : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (a b : ℝ) (hb : 0 ≤ b)
    (hP : ∀ x, P.step f x ≤ f x+a) (hQ : ∀ x, Q.step f x ≤ f x+b) (x : α) :
    P.poissonized t (fun y => Q.poissonized u f y) x ≤ f x+(t:ℝ)*a+(u:ℝ)*b := by
  have h := P.poissonized_mono t (fun y => Q.poissonized u f y) (fun y => f y+(u:ℝ)*b)
    (Q.poissonized_nonneg u f hf) (fun y => add_nonneg (hf y) (mul_nonneg u.coe_nonneg hb))
    (Q.poissonized_drift_bound u f b hf hQ) x
  rw [P.poissonized_add t f (fun _ => (u:ℝ)*b) hf (fun _ => mul_nonneg u.coe_nonneg hb),P.poissonized_const] at h
  exact h.trans (add_le_add (P.poissonized_drift_bound t f a hf hP x) le_rfl)

theorem finite_three_clock_drift {α : Type*} [Fintype α] (P Q R : FiniteKernel α)
    (t u v : NNReal) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hP : ∀ x, P.step f x ≤ f x+a) (hQ : ∀ x, Q.step f x ≤ f x+b)
    (hR : ∀ x, R.step f x ≤ f x+c) (x : α) :
    P.poissonized t (fun y => Q.poissonized u (fun z => R.poissonized v f z) y) x ≤
      f x+(t:ℝ)*a+(u:ℝ)*b+(v:ℝ)*c := by
  have hconst : 0 ≤ (u:ℝ)*b+(v:ℝ)*c := add_nonneg (mul_nonneg u.coe_nonneg hb) (mul_nonneg v.coe_nonneg hc)
  have h := P.poissonized_mono t (fun y => Q.poissonized u (fun z => R.poissonized v f z) y)
    (fun y => f y+((u:ℝ)*b+(v:ℝ)*c))
    (Q.poissonized_nonneg u _ (R.poissonized_nonneg v f hf)) (fun y => add_nonneg (hf y) hconst)
    (fun y => by simpa only [add_assoc] using finite_two_clock_drift Q R u v f hf b c hc hQ hR y) x
  rw [P.poissonized_add t f (fun _ => (u:ℝ)*b+(v:ℝ)*c) hf (fun _ => hconst),P.poissonized_const] at h
  have hh := h.trans (add_le_add (P.poissonized_drift_bound t f a hf hP x) le_rfl)
  simpa only [add_assoc] using hh

theorem finite_three_clock_mono {α : Type*} [Fintype α] (P Q R : FiniteKernel α)
    (t u v : NNReal) (f g : α → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfg : ∀ x, f x ≤ g x) (x : α) :
    P.poissonized t (fun y => Q.poissonized u (fun z => R.poissonized v f z) y) x ≤
    P.poissonized t (fun y => Q.poissonized u (fun z => R.poissonized v g z) y) x := by
  have hR := R.poissonized_mono v f g hf hg hfg
  have hQ := Q.poissonized_mono u _ _ (R.poissonized_nonneg v f hf) (R.poissonized_nonneg v g hg) hR
  exact P.poissonized_mono t _ _
    (Q.poissonized_nonneg u _ (R.poissonized_nonneg v f hf))
    (Q.poissonized_nonneg u _ (R.poissonized_nonneg v g hg)) hQ x

end
end FiniteCopyReactor

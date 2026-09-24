import proofs.FiniteCopyReactor.KernelEmbedding

namespace FiniteCopyReactor
noncomputable section
open Classical FiniteCopy
open scoped ENNReal BigOperators

theorem marked_state_law_independent {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (f : α → ℝ) (n : ℕ) (x : α) (z w : ℝ) :
    P.law n (fun y _ => f y) x z=P.law n (fun y _ => f y) x w := by
  induction n generalizing x z w with
  | zero => rfl
  | succ n ih =>
    change (∑ b,P.prob x b*P.law n (fun y _ => f y) (P.next x b) (z+P.mark b))=
      ∑ b,P.prob x b*P.law n (fun y _ => f y) (P.next x b) (w+P.mark b)
    apply Finset.sum_congr rfl
    intro b _
    rw [ih (P.next x b) (z+P.mark b) (w+P.mark b)]

theorem marked_state_poisson_independent {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (t : NNReal) (f : α → ℝ) (x : α) (z w : ℝ) :
    P.poissonized t (fun y _ => f y) x z=P.poissonized t (fun y _ => f y) x w := by
  unfold MarkedKernel.poissonized
  apply tsum_congr
  intro n
  rw [marked_state_law_independent P f n x z w]

def threeClock {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (q t u v : ℝ) (f : α → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  causalClockEndpoint P q (fun y => causalClockEndpoint Q q
    (fun w => causalClockEndpoint R q f w v) y u) x t

theorem three_clock_map {α γ β : Type*} [Fintype β]
    (P Q R : MarkedKernel α β) (P' Q' R' : MarkedKernel γ β) (φ : α → γ) (q : ℝ)
    (hP : ∀ f x t, causalClockEndpoint P q (fun y => f (φ y)) x t = causalClockEndpoint P' q f (φ x) t)
    (hQ : ∀ f x t, causalClockEndpoint Q q (fun y => f (φ y)) x t = causalClockEndpoint Q' q f (φ x) t)
    (hR : ∀ f x t, causalClockEndpoint R q (fun y => f (φ y)) x t = causalClockEndpoint R' q f (φ x) t)
    (t u v : ℝ) (f : γ → ℝ≥0∞) (x : α) :
    threeClock P Q R q t u v (fun y => f (φ y)) x = threeClock P' Q' R' q t u v f (φ x) := by
  unfold threeClock
  simp_rw [hR f]
  simp_rw [hQ (fun y => causalClockEndpoint R' q f y v)]
  exact hP (fun y => causalClockEndpoint Q' q (fun z => causalClockEndpoint R' q f z v) y u) x t

theorem causal_clock_real_nn {α β : Type*} [Fintype β] (P : MarkedKernel α β) (q T : NNReal)
    (f : α → ℝ) (C : ℝ) (hf : ∀ y,0 ≤ f y ∧ f y ≤ C) (x : α) (z : ℝ) :
    causalClockEndpoint P q (fun y => ENNReal.ofReal (f y)) x T=
      ENNReal.ofReal (P.poissonized (q*T) (fun y _ => f y) x z) := by
  have hT : (0:ℝ) ≤ (T:ℝ) := T.property
  simp only [causalClockEndpoint,hT,if_true]
  exact clock_endpoint_real_nn P q T f C hf x z

theorem three_clock_real_nn {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (q t u v : NNReal) (f : α → ℝ) (hf : ∀ y,0 ≤ f y ∧ f y ≤ 1) (x : α) :
    threeClock P Q R q t u v (fun y => ENNReal.ofReal (f y)) x=
      ENNReal.ofReal (threeStage P Q R (q*t) (q*u) (q*v) (fun y _ => f y) x 0) := by
  let gR := fun y => R.poissonized (q*v) (fun w _ => f w) y 0
  let gQ := fun y => Q.poissonized (q*u) (fun w _ => gR w) y 0
  have hR1 (y) : 0 ≤ gR y ∧ gR y ≤ 1 := marked_poisson_bounds R _ 1 (fun w _ => hf w) (q*v) y 0
  have hQ1 (y) : 0 ≤ gQ y ∧ gQ y ≤ 1 := marked_poisson_bounds Q _ 1 (fun w _ => hR1 w) (q*u) y 0
  have hR (y a) : R.poissonized (q*v) (fun w _ => f w) y a=gR y :=
    marked_state_poisson_independent R (q*v) f y a 0
  have hQ (y a) : Q.poissonized (q*u) (fun w _ => gR w) y a=gQ y :=
    marked_state_poisson_independent Q (q*u) gR y a 0
  have he : threeStage P Q R (q*t) (q*u) (q*v) (fun y _ => f y) x 0=
      P.poissonized (q*t) (fun y _ => gQ y) x 0 := by
    unfold threeStage
    apply congrArg (fun h : α → ℝ → ℝ => P.poissonized (q*t) h x 0)
    funext y a
    have hfun : (fun w b => R.poissonized (q*v) (fun z _ => f z) w b)=(fun w _ => gR w) := by
      funext w b
      exact hR w b
    rw [hfun]
    exact hQ y a
  rw [he]
  unfold threeClock
  simp_rw [causal_clock_real_nn R q v f 1 hf _ 0]
  change causalClockEndpoint P q (fun y => causalClockEndpoint Q q
    (fun w => ENNReal.ofReal (gR w)) y u) x t = _
  simp_rw [causal_clock_real_nn Q q u gR 1 hR1 _ 0]
  exact causal_clock_real_nn P q t gQ 1 hQ1 x 0

end
end FiniteCopyReactor

import proofs.CompositionalMemory.FiniteSmoothRecovery

namespace CompositionalMemory
open FiniteCopy HeritableCompositions
open scoped Matrix.Norms.Operator

theorem finite_time_semigroup {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (s t : NNReal) (f : α → ℝ) (x : α) :
    finiteTimeExpectation M (s+t) f x =
      finiteTimeExpectation M s (fun y => finiteTimeExpectation M t f y) x := by
  unfold finiteTimeExpectation
  rw [NNReal.coe_add,add_smul,Matrix.exp_add_of_commute _ _
    (((Commute.refl (jumpGeneratorMatrix M)).smul_left (s : ℝ)).smul_right (t : ℝ)),
    Matrix.mulVec_mulVec]

theorem finite_time_add_constant {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (t : NNReal) (f : α → ℝ)
    (c : ℝ) (x : α) :
    finiteTimeExpectation M t (fun y => f y+c) x = finiteTimeExpectation M t f x+c := by
  have hc : finiteTimeExpectation M t (fun _ => c) x=c := by
    obtain ⟨q,hq,_,hb⟩ := M.exists_clock 0
    rw [finite_time_eq_uniformized M q t hq hb]
    exact poisson_constant _ _ c x
  unfold finiteTimeExpectation at hc ⊢
  simp only [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]
  exact congrArg (fun z => (∑ y,NormedSpace.exp ((t : ℝ) • jumpGeneratorMatrix M) x y*f y)+z) hc

/-- Join finitely many local time certificates using their shared endpoint
observables. No differentiability across polynomial joins is assumed. -/
theorem finite_recovery_chain {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (M : FiniteJumpModel α β) (dt : ℕ → NNReal)
    (v : ℕ → α → ℝ) (cost : ℕ → ℝ) (n : ℕ)
    (hstage : ∀ i<n, ∀ x, finiteTimeExpectation M (dt i) (v (i+1)) x ≤ v i x+cost i)
    (x : α) :
    finiteTimeExpectation M (∑ i ∈ Finset.range n,dt i) (v n) x ≤
      v 0 x+∑ i ∈ Finset.range n,cost i := by
  induction n with
  | zero => simp [finiteTimeExpectation]
  | succ n ih =>
    rw [Finset.sum_range_succ,finite_time_semigroup]
    have hm := finite_time_expectation_mono M (∑ i ∈ Finset.range n,dt i)
      (fun y => finiteTimeExpectation M (dt n) (v (n+1)) y)
      (fun y => v n y+cost n) (hstage n (Nat.lt_succ_self n)) x
    rw [finite_time_add_constant] at hm
    have hp := ih (fun i hi => hstage i (Nat.lt_succ_of_lt hi))
    rw [Finset.sum_range_succ]
    linarith only [hm,hp]

end CompositionalMemory

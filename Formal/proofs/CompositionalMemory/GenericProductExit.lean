import proofs.CompositionalMemory.GenericRetainedReactions

namespace CompositionalMemory
open FiniteCopy

theorem reaction_generator_sum {S R ι : Type*} [Fintype R] [Fintype ι]
    (next : S → R → S) (rate : S → R → ℝ) (W : ι → S → ℝ) (s : S) :
    reactionGenerator next rate (fun x => ∑ i, W i x) s =
      ∑ i, reactionGenerator next rate (W i) s := by
  unfold reactionGenerator
  simp_rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- First-departure product bound for a literal retained reaction law.
The module count multiplies the error outside the exponential. -/
theorem retained_product_exit_bound {S R : Type*} [Fintype R] [DecidableEq S]
    {k : ℕ} (next : S → R → S) (rate : S → R → ℝ) (hrate : ∀ s r, 0 ≤ rate s r)
    (active : S → Prop) (D : Finset S) (E : Fin k → S → ℝ)
    (α N a b C : ℝ) (hα : 0 ≤ α) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hdeparture : ∀ s ∈ D, active s → ∀ r, next s r ∉ D → ∃ i, b ≤ E i (next s r))
    (hgen : ∀ s ∈ D, active s → ∀ i,
      reactionGenerator next rate (fun x => Real.exp (α*N*E i x)) s ≤ C)
    (q t : NNReal) (hq : 0 < (q : ℝ))
    (hclock : ∀ s, (retainedReactionModel next rate hrate active D).total s ≤ q)
    (s : {s : S // s ∈ D}) (hstart : ∀ i, E i s.val ≤ a) :
    Real.exp (α*N*b)*((retainedReactionModel next rate hrate active D).uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {none}) (some s) ≤ (k:ℝ)*(Real.exp (α*N*a)+(t:ℝ)*C) := by
  let W := fun i x => Real.exp (α*N*E i x)
  have hsum (x) : 0 ≤ ∑ i, W i x := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hb (x) (hx : x ∈ D) (ha : active x) (r) (hr : next x r ∉ D) :
      Real.exp (α*N*b) ≤ ∑ i, W i (next x r) := by
    obtain ⟨i,hi⟩ := hdeparture x hx ha r hr
    have he : Real.exp (α*N*b) ≤ W i (next x r) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (mul_nonneg hα hN))
    exact he.trans (Finset.single_le_sum
      (fun j _ => (show 0 ≤ W j (next x r) from (Real.exp_pos _).le)) (Finset.mem_univ i))
  have hg (x) (hx : x ∈ D) (ha : active x) :
      reactionGenerator next rate (fun y => ∑ i, W i y) x ≤ (k:ℝ)*C := by
    rw [reaction_generator_sum]
    calc
      _ ≤ ∑ _i : Fin k, C := Finset.sum_le_sum (fun i _ => hgen x hx ha i)
      _ = _ := by simp
  have h := retained_reaction_event_bound next rate hrate active D (fun y => ∑ i, W i y)
    (Real.exp (α*N*b)) ((k:ℝ)*C) (Real.exp_pos _).le (by positivity)
    (fun x _ => hsum x) hb hg q t hq hclock s
  have hs : ∑ i, W i s.val ≤ (k:ℝ)*Real.exp (α*N*a) := by
    calc
      _ ≤ ∑ _i : Fin k, Real.exp (α*N*a) := Finset.sum_le_sum (fun i _ =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hstart i) (mul_nonneg hα hN)))
      _ = _ := by simp
  nlinarith only [h,hs]

end CompositionalMemory

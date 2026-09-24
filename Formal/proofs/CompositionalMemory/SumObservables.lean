import proofs.FiniteCopy.UniformizedBounds
import proofs.HeritableCompositions.AffineRecovery

namespace CompositionalMemory
open FiniteCopy

theorem generator_sum_observables {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    (M : FiniteJumpModel α β) (W : ι → α → ℝ) (x : α) :
    M.generator (fun y => ∑ i, W i y) x = ∑ i, M.generator (W i) x := by
  unfold FiniteJumpModel.generator
  simp_rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Sum the exponentials, not the energies: this retains the per-module exponent. -/
theorem product_event_bound {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    {k : ℕ} (M : FiniteJumpModel α β) (W : Fin k → α → ℝ)
    (q t : NNReal) (hq : 0 < (q : ℝ)) (hclock : ∀ x, M.total x ≤ q)
    (a b w0 : ℝ) (hW : ∀ i x, 0 ≤ W i x)
    (hgen : ∀ i x, M.generator (W i) x ≤ b) (x : α)
    (hstart : ∀ i, W i x ≤ w0) :
    a*(M.uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {y | ∃ i, a ≤ W i y}) x ≤
      (k : ℝ)*(w0+(t : ℝ)*b) := by
  have hsum (y) : 0 ≤ ∑ i, W i y := Finset.sum_nonneg (fun i _ => hW i y)
  have hA (y : α) (hy : y ∈ {y | ∃ i, a ≤ W i y}) : a ≤ ∑ i, W i y := by
    obtain ⟨i,hi⟩ := hy
    exact hi.trans (Finset.single_le_sum (fun j _ => hW j y) (Finset.mem_univ i))
  have hg (y) : M.generator (fun z => ∑ i, W i z) y ≤ (k : ℝ)*b := by
    rw [generator_sum_observables]
    calc
      _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => hgen i y)
      _ = _ := by simp
  have h := M.uniformized_event_bound q t hq hclock {y | ∃ i, a ≤ W i y}
    (fun y => ∑ i, W i y) a ((k : ℝ)*b) hsum hA hg x
  have hs : ∑ i, W i x ≤ (k : ℝ)*w0 := by
    calc
      _ ≤ ∑ _i : Fin k, w0 := Finset.sum_le_sum (fun i _ => hstart i)
      _ = _ := by simp
  nlinarith only [h,hs]

/-- Recovery for all coordinates under one common stopped law. -/
theorem product_recovery_bound {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    {k : ℕ} (M : FiniteJumpModel α β) (W : Fin k → α → ℝ)
    (q t : NNReal) (hq : 0 < (q : ℝ)) (hclock : ∀ x, M.total x ≤ q)
    (a decay C w0 : ℝ) (hW : ∀ i x, 0 ≤ W i x)
    (hdecay : decay ≤ q) (hC : 0 ≤ C)
    (hgen : ∀ i x, M.generator (W i) x ≤ -decay*W i x+decay*C)
    (x : α) (hstart : ∀ i, W i x ≤ w0) :
    a*(M.uniformize q hq hclock).poissonized (q*t)
      (FiniteKernel.eventIndicator {y | ∃ i, a ≤ W i y}) x ≤
      (k : ℝ)*(Real.exp (-decay*(t : ℝ))*w0+C) := by
  have hsum (y) : 0 ≤ ∑ i, W i y := Finset.sum_nonneg (fun i _ => hW i y)
  have hA (y : α) (hy : y ∈ {y | ∃ i, a ≤ W i y}) : a ≤ ∑ i, W i y := by
    obtain ⟨i,hi⟩ := hy
    exact hi.trans (Finset.single_le_sum (fun j _ => hW j y) (Finset.mem_univ i))
  have hg (y) : M.generator (fun z => ∑ i, W i z) y ≤
      -decay*(∑ i, W i y)+decay*((k : ℝ)*C) := by
    rw [generator_sum_observables]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hgen i y)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
    nlinarith only [h]
  have h := HeritableCompositions.uniformized_event_affine M q t hq hclock
    {y | ∃ i, a ≤ W i y} (fun y => ∑ i, W i y) a decay ((k : ℝ)*C)
    hsum hA hdecay (by positivity) hg x
  have hs : ∑ i, W i x ≤ (k : ℝ)*w0 := by
    calc
      _ ≤ ∑ _i : Fin k, w0 := Finset.sum_le_sum (fun i _ => hstart i)
      _ = _ := by simp
  have hs' := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-decay*(t : ℝ))).le
  nlinarith only [h,hs']

end CompositionalMemory

import proofs.OptimalAffinityRealizability.GlobalMaximum

namespace OptimalAffinityRealizability
open scoped BigOperators
noncomputable section

theorem commonResponseCurrent_one_nonnegative {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : Matrix ι ι ℝ) (f q x : ι → ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hf : ∀ i, 0 < f i)
    (hq : ∀ i, 1 < q i)
    (hr : ∀ i, T.transpose.mulVec f i = q i * f i)
    (ht : ∀ i, normalizedResponseCurrent T q x i = 1) :
    (∀ i, 0 ≤ x i) ∧ ∃ k, x k = 0 := by
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ
    (fun i => x i / f i) Finset.univ_nonempty
  have hc := Real.exp_le_exp.mpr (responseMinimum_comparison T f q x hT hf hr k
    (fun i => hk i (Finset.mem_univ i)))
  have he := (div_eq_one_iff_eq (ne_of_gt (sub_pos.mpr (hq k)))).mp (ht k)
  have hs := exp_tangent_gap_nonneg (a := x k) (hq k)
  have hzero : x k = 0 := (exp_tangent_gap_eq_zero_iff (hq k)).mp (by
    change q k * Real.exp (x k) - Real.exp (T.transpose.mulVec x k) = q k - 1 at he
    linarith)
  refine ⟨?_, k, hzero⟩
  intro i
  have h := hk i (Finset.mem_univ i)
  rw [hzero, zero_div] at h
  simpa using (le_div_iff₀ (hf i)).mp h

theorem commonResponseCurrent_zero_propagates {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (q x : ι → ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hq : ∀ i, 1 < q i)
    (hx : ∀ i, 0 ≤ x i)
    (ht : ∀ i, normalizedResponseCurrent T q x i = 1)
    (i j : ι) (hi : x i = 0) (hij : 0 < T j i) : x j = 0 := by
  have he := (div_eq_one_iff_eq (ne_of_gt (sub_pos.mpr (hq i)))).mp (ht i)
  change q i * Real.exp (x i) - Real.exp (T.transpose.mulVec x i) = q i - 1 at he
  rw [hi, Real.exp_zero, mul_one] at he
  have hs : T.transpose.mulVec x i = 0 := Real.exp_injective (by
    rw [Real.exp_zero]
    linarith)
  have hterm : T j i * x j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hT k i) (hx k))).mp hs j
      (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hij)

def ResponseStronglyConnected {ι : Type*} (T : Matrix ι ι ℝ) : Prop :=
  ∀ i j, Relation.ReflTransGen (fun a b => 0 < T b a) i j

theorem commonResponseCurrent_one_eq_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (T : Matrix ι ι ℝ) (f q x : ι → ℝ)
    (hT : ∀ i j, 0 ≤ T i j) (hf : ∀ i, 0 < f i)
    (hq : ∀ i, 1 < q i)
    (hr : ∀ i, T.transpose.mulVec f i = q i * f i)
    (ht : ∀ i, normalizedResponseCurrent T q x i = 1)
    (hconn : ResponseStronglyConnected T) : x = 0 := by
  obtain ⟨hx, k, hk⟩ := commonResponseCurrent_one_nonnegative T f q x hT hf hq hr ht
  funext j
  have hp := hconn k j
  induction hp with
  | refl => exact hk
  | @tail b c _ hbc ih =>
      exact commonResponseCurrent_zero_propagates T q x hT hq hx ht b c ih hbc

theorem reconstructedSource_uniqueGlobal {n : ℕ} [Nonempty (Fin n)]
    (source : SquareSource n) (J : ℝ) (g f q : Fin n → ℝ)
    (hJ : 0 < J) (hg : ∀ i, 0 < g i)
    (hmode : ControlledProductionMode source g)
    (hT : ∀ i j, 0 ≤ responseMatrix source i j)
    (hf : ∀ i, 0 < f i) (hq : ∀ i, 1 < q i)
    (hr : ∀ i, (responseMatrix source).transpose.mulVec f i = q i * f i)
    (hconn : ResponseStronglyConnected (responseMatrix source))
    (z : Fin n → ℝ) (hz : GlobalStationaryFiber source J g q z)
    (heq : controlledFluxAtLogState source J g q z = J) : z = 0 := by
  have ht := stationary_commonResponseCurrent source J g q z hJ hg hmode hz
  simp only [heq, div_self (ne_of_gt hJ)] at ht
  have hx := commonResponseCurrent_one_eq_zero (responseMatrix source) f q
    (source.reactant.transpose.mulVec z) hT hf hq hr ht hconn
  apply reactantTranspose_mulVec_injective source
  simpa using hx

end
end OptimalAffinityRealizability

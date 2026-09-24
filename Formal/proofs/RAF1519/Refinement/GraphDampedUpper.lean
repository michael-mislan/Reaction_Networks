import proofs.RAF1519.Refinement.GraphLinearBarrier

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

/-- Heterogeneous killing rates retain a uniform exponential comparison. -/
theorem graph_damped_upper {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (κ : ι → ℝ) (a : ℝ) (ha : 0 < a) (hκ : ∀ i, a ≤ κ i)
    (f v : ℝ → ι → ℝ) (T q c L : ℝ) (hc0 : 0 ≤ c) (hL : 0 ≤ L)
    (hc : ∀ i, ContinuousOn (fun t => f t i) (Set.Icc 0 T))
    (hd : ∀ t ∈ Set.Ico 0 T, ∀ i, HasDerivWithinAt (fun u => f u i) (v t i) (Set.Ici t) t)
    (h0 : ∀ i, f 0 i ≤ q+c)
    (hv : ∀ t ∈ Set.Ico 0 T, ∀ i, v t i ≤ graphDiffusion k (f t) i-κ i*(f t i-q)+L) :
    ∀ t ∈ Set.Icc 0 T, ∀ i, f t i ≤ q+c*Real.exp (-a*t)+L/a := by
  let B := fun t => q+c*Real.exp (-a*t)+L/a
  have hB (t : ℝ) : HasDerivAt B (-a*c*Real.exp (-a*t)) t := by
    simpa [B,mul_assoc,mul_comm,mul_left_comm] using
      (((((hasDerivAt_id t).const_mul (-a)).exp).const_mul c).const_add q).add_const (L/a)
  have hvw : ∀ t ∈ Set.Ico 0 T, ∀ i, 0 < f t i-B t →
      v t i+a*c*Real.exp (-a*t) ≤ ∑ j, k i j*((f t j-B t)-(f t i-B t)) := by
    intro t ht i hi
    change v t i+a*c*Real.exp (-a*t) ≤ graphDiffusion k (fun j => f t j-B t) i
    rw [graphDiffusion_sub_const]
    have he : 0 ≤ c*Real.exp (-a*t) := mul_nonneg hc0 (Real.exp_pos _).le
    have hLa : 0 ≤ L/a := div_nonneg hL ha.le
    have hf : 0 ≤ f t i-q := by dsimp [B] at hi; linarith
    have hm := mul_le_mul_of_nonneg_right (hκ i) hf
    have heq : a*(L/a)=L := by field_simp
    have hmul := mul_pos ha hi
    dsimp [B] at hmul
    nlinarith [hv t ht i]
  have hb := graph_right_barrier k hk hsym (fun t i => f t i-B t)
    (fun t i => v t i+a*c*Real.exp (-a*t)) T
    (fun i => (hc i).sub (fun t _ => (hB t).continuousAt.continuousWithinAt))
    (fun t ht i => by simpa only [sub_neg_eq_add,neg_mul] using (hd t ht i).sub (hB t).hasDerivWithinAt)
    (fun i => by dsimp [B]; simp only [mul_zero,Real.exp_zero,mul_one]; have := div_nonneg hL ha.le; linarith [h0 i]) hvw
  intro t ht i
  have hh := hb t ht i
  dsimp [B] at hh
  linarith

end
end RAF1519.Refinement

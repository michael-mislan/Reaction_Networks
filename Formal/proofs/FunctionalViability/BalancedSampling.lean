import proofs.FunctionalViability.Sampling

namespace FunctionalViability.Robust
noncomputable section

/-- Terminal source events: inactive, not activated, no progeny, unrecorded,
recorded qualifying progeny. Conditional probabilities multiply along a path. -/
def stagePath (p x y r : ℝ) : Fin 5 → ℝ :=
  ![1-p, p*(1-x), p*x*(1-y), p*x*y*(1-r), p*x*y*r]
def stageNegative : Fin 5 → Bool := ![true,true,true,true,false]

theorem stage_normalized (p x y r : ℝ) : ∑ i, stagePath p x y r i = 1 := by
  simp [stagePath, Fin.sum_univ_succ]; ring

theorem stage_nonnegative (p x y r : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    ∀ i, 0 ≤ stagePath p x y r i := by
  rcases hp with ⟨hp,hp1⟩
  rcases hx with ⟨hx,hx1⟩
  rcases hy with ⟨hy,hy1⟩
  rcases hr with ⟨hr,hr1⟩
  have hp' : 0 ≤ 1-p := by linarith
  have hx' : 0 ≤ 1-x := by linarith
  have hy' : 0 ≤ 1-y := by linarith
  have hr' : 0 ≤ 1-r := by linarith
  intro i
  fin_cases i
  · exact hp'
  · change 0 ≤ p*(1-x); positivity
  · change 0 ≤ p*x*(1-y); positivity
  · change 0 ≤ p*x*y*(1-r); positivity
  · change 0 ≤ p*x*y*r; positivity

theorem stage_negative (p x y r : ℝ) :
    (∑ i, if stageNegative i then stagePath p x y r i else 0)=1-p*(x*y*r) := by
  norm_num [stageNegative,stagePath,Fin.sum_univ_succ]; ring

def recordedMean {K : Type*} [Fintype K] (μ x y r : K → ℝ) : ℝ :=
  ∑ k, μ k*(x k*y k*r k)
def stageMixture {K : Type*} (μ x y r : K → ℝ) (p : ℝ) (i : K × Fin 5) : ℝ :=
  μ i.1 * stagePath p (x i.1) (y i.1) (r i.1) i.2

theorem stage_mixture_normalized {K : Type*} [Fintype K]
    (μ x y r : K → ℝ) (p : ℝ) (hs : ∑ k, μ k=1) :
    ∑ i, stageMixture μ x y r p i = 1 := by
  simp only [stageMixture,Fintype.sum_prod_type,← Finset.mul_sum,stage_normalized,mul_one]
  exact hs

theorem stage_mixture_negative {K : Type*} [Fintype K]
    (μ x y r : K → ℝ) (p : ℝ) (hs : ∑ k, μ k=1) :
    (∑ i, if stageNegative i.2 then stageMixture μ x y r p i else 0)=
      1-p*recordedMean μ x y r := by
  simp only [Fintype.sum_prod_type,stageMixture]
  have hi (k : K) :
      (∑ j, if stageNegative j then μ k*stagePath p (x k) (y k) (r k) j else 0)=
        μ k*(1-p*(x k*y k*r k)) := by
    rw [← stage_negative, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all
  simp_rw [hi]
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,recordedMean]
  rw [hs, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Independent fixed groups: product of the two explicit history event masses. -/
def balancedNegative {K : Type*} [Fintype K]
    (μ x y a b r s : K → ℝ) (p : ℝ) (m : ℕ) : ℝ :=
  allNegative (stageMixture μ x y r p) (fun i => stageNegative i.2) m *
  allNegative (stageMixture μ a b s p) (fun i => stageNegative i.2) m

theorem balanced_identity {K : Type*} [Fintype K]
    (μ x y a b r s : K → ℝ) (p : ℝ) (m : ℕ) (hs : ∑ k, μ k=1) :
    balancedNegative μ x y a b r s p m =
      (1-p*recordedMean μ x y r)^m*(1-p*recordedMean μ a b s)^m := by
  simp only [balancedNegative,negative_factorization,
    stage_mixture_negative μ x y r p hs,stage_mixture_negative μ a b s p hs]

theorem balanced_bound (u v p theta g : ℝ) (m : ℕ)
    (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p)
    (hg : 0 ≤ g) (havg : g ≤ (u+v)/2) :
    (1-p*u)^m*(1-p*v)^m ≤ (1-theta*g)^(2*m) := by
  have hpu := mul_le_one₀ hp.2 hu.1 hu.2
  have hpv := mul_le_one₀ hp.2 hv.1 hv.2
  have havg0 : 0 ≤ (u+v)/2 := by linarith [hu.1,hv.1]
  have havg1 : (u+v)/2 ≤ 1 := by linarith [hu.2,hv.2]
  have hpa := mul_le_one₀ hp.2 havg0 havg1
  have hgm := mul_le_mul ht.2 havg hg hp.1
  have hbase : (1-p*u)*(1-p*v) ≤ (1-theta*g)^2 := by
    have hi : (1-p*(u+v)/2)^2-(1-p*u)*(1-p*v)=p^2*(u-v)^2/4 := by ring
    have hz := mul_nonneg (sq_nonneg p) (sq_nonneg (u-v))
    have hb : 0 ≤ 1-p*(u+v)/2 := by nlinarith
    have hc : 1-p*(u+v)/2 ≤ 1-theta*g := by nlinarith
    nlinarith [sq_nonneg (1-theta*g-(1-p*(u+v)/2))]
  rw [← mul_pow, pow_mul]
  exact pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hbase m

end
end FunctionalViability.Robust

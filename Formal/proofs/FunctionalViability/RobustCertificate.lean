import proofs.FunctionalViability.CoverageBounds
import proofs.FunctionalViability.BalancedSampling

namespace FunctionalViability.Robust
noncomputable section

structure Stages where
  x : ℝ
  y : ℝ
  a : ℝ
  b : ℝ
  r : ℝ
  s : ℝ
  hx : 0 ≤ x ∧ x ≤ 1
  hy : 0 ≤ y ∧ y ≤ 1
  ha : 0 ≤ a ∧ a ≤ 1
  hb : 0 ≤ b ∧ b ≤ 1
  hr : 0 ≤ r ∧ r ≤ 1
  hs : 0 ≤ s ∧ s ≤ 1

/-- Only source constraints are fields; no detection-floor hypothesis is stored. -/
structure Population (K : Type*) [Fintype K] (c d kappa eta : ℝ) where
  μ : K → ℝ
  z : K → Stages
  covered : K → Bool
  nonneg : ∀ k, 0 ≤ μ k
  normalized : ∑ k, μ k = 1
  mass : 1-eta ≤ ∑ k, if covered k then μ k else 0
  coverage : ∀ k, covered k = true → Admissible c d (z k).x (z k).y (z k).a (z k).b
  recording : ∀ k, covered k = true → kappa ≤ (z k).r ∧ kappa ≤ (z k).s

def usableFloor (c d kappa eta : ℝ) := (1-eta)*kappa*recoveryFloor c d

theorem triple_bounds (x y r : ℝ) (hx : 0 ≤ x ∧ x ≤ 1)
    (hy : 0 ≤ y ∧ y ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    0 ≤ x*y*r ∧ x*y*r ≤ 1 := by
  exact ⟨mul_nonneg (mul_nonneg hx.1 hy.1) hr.1,
    mul_le_one₀ (mul_le_one₀ hx.2 hy.1 hy.2) hr.1 hr.2⟩

theorem mean_bounds {K : Type*} [Fintype K] (μ x y r : K → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (hs : ∑ k, μ k=1)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (hy : ∀ k, 0 ≤ y k ∧ y k ≤ 1)
    (hr : ∀ k, 0 ≤ r k ∧ r k ≤ 1) :
    0 ≤ recordedMean μ x y r ∧ recordedMean μ x y r ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hμ k) (triple_bounds _ _ _ (hx k) (hy k) (hr k)).1)
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      mul_le_mul_of_nonneg_left (triple_bounds _ _ _ (hx k) (hy k) (hr k)).2 (hμ k))
    simpa [recordedMean,hs] using h

theorem recorded_coverage (c d kappa : ℝ) (z : Stages)
    (hc : 0 ≤ c) (hk : 0 ≤ kappa)
    (hcov : Admissible c d z.x z.y z.a z.b) (hr : kappa ≤ z.r) (hs : kappa ≤ z.s) :
    kappa*recoveryFloor c d ≤ (z.x*z.y*z.r+z.a*z.b*z.s)/2 := by
  have h := mul_le_mul_of_nonneg_left (coverage_bound _ _ _ _ _ _ hc hcov) hk
  have h1 := mul_le_mul_of_nonneg_left hr (mul_nonneg z.hx.1 z.hy.1)
  have h2 := mul_le_mul_of_nonneg_left hs (mul_nonneg z.ha.1 z.hb.1)
  nlinarith

theorem population_floor {K : Type*} [Fintype K] {c d kappa eta : ℝ}
    (M : Population K c d kappa eta) (hc : 0 ≤ c) (hk : 0 ≤ kappa) :
    usableFloor c d kappa eta ≤
      (recordedMean M.μ (fun k => (M.z k).x) (fun k => (M.z k).y) (fun k => (M.z k).r) +
       recordedMean M.μ (fun k => (M.z k).a) (fun k => (M.z k).b) (fun k => (M.z k).s))/2 := by
  let L := kappa*recoveryFloor c d
  have hL : 0 ≤ L := mul_nonneg hk (floor_nonnegative c d)
  have hp (k : K) :
      (if M.covered k then M.μ k else 0)*L ≤
        M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+(M.z k).a*(M.z k).b*(M.z k).s)/2 := by
    cases he : M.covered k
    · simp only [Bool.false_eq_true,↓reduceIte,zero_mul]
      exact div_nonneg (mul_nonneg (M.nonneg k) (add_nonneg
        (triple_bounds _ _ _ (M.z k).hx (M.z k).hy (M.z k).hr).1
        (triple_bounds _ _ _ (M.z k).ha (M.z k).hb (M.z k).hs).1)) (by norm_num)
    · simp only [↓reduceIte]
      have h := mul_le_mul_of_nonneg_left
        (recorded_coverage c d kappa (M.z k) hc hk (M.coverage k he)
          (M.recording k he).1 (M.recording k he).2) (M.nonneg k)
      dsimp [L]
      nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hp k)
  have hm := mul_le_mul_of_nonneg_right M.mass hL
  rw [← Finset.sum_mul] at hh
  have he : (∑ k, M.μ k*((M.z k).x*(M.z k).y*(M.z k).r+
      (M.z k).a*(M.z k).b*(M.z k).s)/2) =
      (recordedMean M.μ (fun k => (M.z k).x) (fun k => (M.z k).y) (fun k => (M.z k).r)+
       recordedMean M.μ (fun k => (M.z k).a) (fun k => (M.z k).b) (fun k => (M.z k).s))/2 := by
    simp only [recordedMean,mul_add,add_div,Finset.sum_add_distrib,Finset.sum_div]
  rw [he] at hh
  unfold usableFloor
  dsimp [L] at hm
  nlinarith

def experiment {K : Type*} [Fintype K] {c d kappa eta : ℝ}
    (M : Population K c d kappa eta) (p : ℝ) (m : ℕ) :=
  balancedNegative M.μ (fun k => (M.z k).x) (fun k => (M.z k).y)
    (fun k => (M.z k).a) (fun k => (M.z k).b)
    (fun k => (M.z k).r) (fun k => (M.z k).s) p m

theorem robust_source_certificate {K : Type*} [Fintype K] {c d kappa eta : ℝ}
    (M : Population K c d kappa eta) (p theta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (hk : 0 ≤ kappa) (heta : eta ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p) :
    experiment M p m ≤ (1-theta*usableFloor c d kappa eta)^(2*m) := by
  unfold experiment
  rw [balanced_identity _ _ _ _ _ _ _ _ _ M.normalized]
  apply balanced_bound
  · exact mean_bounds _ _ _ _ M.nonneg M.normalized (fun k => (M.z k).hx)
      (fun k => (M.z k).hy) (fun k => (M.z k).hr)
  · exact mean_bounds _ _ _ _ M.nonneg M.normalized (fun k => (M.z k).ha)
      (fun k => (M.z k).hb) (fun k => (M.z k).hs)
  · exact hp
  · exact ht
  · exact mul_nonneg (mul_nonneg (by linarith) hk) (floor_nonnegative c d)
  · exact population_floor M hc hk

theorem sharp_calibration {E : Type*} [Fintype E]
    (ν r : E → ℝ) (good : E → Bool) (B delta : ℝ)
    (hν : ∀ e, 0 ≤ ν e) (hs : ∑ e, ν e=1)
    (hr : ∀ e, r e ≤ 1) (hg : ∀ e, good e=true → r e ≤ B)
    (hB : B ≤ 1) (hb : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e*r e) ≤ delta+(1-delta)*B := by
  have hp (e : E) : ν e*r e ≤ ν e*B+(if good e then 0 else ν e)*(1-B) := by
    cases he : good e
    · simp only [Bool.false_eq_true,↓reduceIte]
      nlinarith [mul_le_mul_of_nonneg_left (hr e) (hν e)]
    · simp only [↓reduceIte,zero_mul,add_zero]
      exact mul_le_mul_of_nonneg_left (hg e he) (hν e)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hp e)
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,hs,one_mul] at hh
  have hd := mul_le_mul_of_nonneg_right hb (show 0 ≤ 1-B by linarith)
  nlinarith

theorem calibrated_robust_certificate {K E : Type*} [Fintype K] [Fintype E]
    {c d kappa eta : ℝ} (M : E → Population K c d kappa eta)
    (ν bad : E → ℝ) (good : E → Bool) (p theta B delta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (hk : 0 ≤ kappa) (heta : eta ≤ 1)
    (hp : 0 ≤ p ∧ p ≤ 1) (ht : 0 ≤ theta ∧ theta ≤ p)
    (hν : ∀ e, 0 ≤ ν e) (hs : ∑ e, ν e=1) (hbad : ∀ e, bad e ≤ 1)
    (hB : B ≤ 1) (budget : (1-theta*usableFloor c d kappa eta)^(2*m) ≤ B)
    (hb : (∑ e, if good e then 0 else ν e) ≤ delta) :
    (∑ e, ν e*(if good e then experiment (M e) p m else bad e)) ≤ delta+(1-delta)*B := by
  have hgood (e : E) : experiment (M e) p m ≤ B :=
    le_trans (robust_source_certificate (M e) p theta m hc hk heta hp ht) budget
  apply sharp_calibration ν _ good B delta hν hs
  · intro e
    cases he : good e
    · simpa using hbad e
    · simpa using le_trans (hgood e) hB
  · intro e he
    simpa [he] using hgood e
  · exact hB
  · exact hb

end
end FunctionalViability.Robust

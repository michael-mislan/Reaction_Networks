import proofs.RobustPermanence.RateAbsorber

namespace RobustPermanence
open CoreCouplingGlobal CoreCouplingCAC

theorem rateField_contDiff (r : AssemblyRates) : ContDiff ℝ 1 (rateField r) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [rateField,rateA,rateB,rateZ,rateH,rateX] <;> fun_prop

theorem rate_extension_solution (r : AssemblyRates) (R : ℝ) (hR : 0 < R) (x₀ : ConsumerVector) :
    ∃ b : ConsumerVector → ℝ, ∃ X : ℝ → ConsumerVector,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (consumerPositivePart (X t)) • rateField r (consumerPositivePart (X t))) t := by
  let b : ContDiffBump (0 : ConsumerVector) := ⟨R,2*R,hR,by linarith⟩
  let f : ConsumerVector → ConsumerVector := fun x => b x • rateField r x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (rateField_contDiff r)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (consumerPositivePart x)) := by
    simpa only [mul_one] using hK.comp consumerPositivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (consumerPositivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem rate_boundary_nonneg (r : AssemblyRates) (hr : RateBox r) (y : ConsumerVector)
    (hy : ∀ i, 0 ≤ y i) (i : Fin 5) (hi : y i = 0) : 0 ≤ rateField r y i := by
  have hA := hy 0
  have hB := hy 1
  have hz := hy 2
  have hH := hy 3
  have ha : 0 ≤ r.a := by linarith [hr.a.1]
  have hb : 0 ≤ r.b := by linarith [hr.b.1]
  have hp : 0 ≤ r.p := by linarith [hr.p.1]
  have hq : 0 ≤ r.q := by linarith [hr.q.1]
  have hef : 0 ≤ r.ef := by linarith [hr.ef.1]
  have her : 0 ≤ r.er := by linarith [hr.er.1]
  have hu : 0 ≤ r.u := by linarith [hr.u.1]
  have hv : 0 ≤ r.v := by linarith [hr.v.1]
  have hh1 : 0 ≤ r.h1 := by linarith [hr.h1.1]
  have hh2 : 0 ≤ r.h2 := by linarith [hr.h2.1]
  fin_cases i
  · change y 0 = 0 at hi
    change 0 ≤ rateA r (y 0) (y 1) (y 2)
    dsimp [rateA]
    rw [hi]
    nlinarith [mul_nonneg (mul_nonneg hq hB) hz,mul_nonneg hef hB]
  · change y 1 = 0 at hi
    change 0 ≤ rateB r (y 0) (y 1) (y 2)
    dsimp [rateB]
    rw [hi]
    nlinarith [mul_nonneg hp hA,mul_nonneg her (sq_nonneg (y 0))]
  · change y 2 = 0 at hi
    change 0 ≤ rateZ r (y 0) (y 1) (y 2) (y 3) (y 4)
    dsimp [rateZ]
    rw [hi]
    nlinarith [mul_nonneg hp hA,mul_nonneg hh1 hH,mul_nonneg hh2 hH]
  · change y 3 = 0 at hi
    change 0 ≤ rateH r (y 2) (y 3)
    dsimp [rateH]
    rw [hi]
    nlinarith [mul_nonneg hu hz,mul_nonneg hv (sq_nonneg (y 2))]
  · change y 4 = 0 at hi
    change 0 ≤ rateX r (y 2) (y 4)
    simp [rateX,hi]

theorem rate_extension_nonnegative (r : AssemblyRates) (hr : RateBox r) (b : ConsumerVector → ℝ)
    (hb : ∀ x, 0 ≤ b x) (X : ℝ → ConsumerVector) (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (consumerPositivePart (X t)) • rateField r (consumerPositivePart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (consumerPositivePart (X t))*rateField r (consumerPositivePart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply rate_boundary_nonneg r hr _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

theorem rate_linear_lower (r : AssemblyRates) (hr : RateBox r) (R : ℝ)
    (hR : 1 ≤ R) (y : ConsumerVector) (hy : ∀ i, 0 ≤ y i) (hy' : ∀ i, y i ≤ R)
    (i : Fin 5) : -(30+10*R)*y i ≤ rateField r y i := by
  have hA := hy 0
  have hB := hy 1
  have hz := hy 2
  have hH := hy 3
  have hX := hy 4
  have hA' := hy' 0
  have hB' := hy' 1
  have hz' := hy' 2
  have hX' := hy' 4
  have hAA : (y 0)^2 ≤ R*y 0 := by nlinarith
  have hzz : (y 2)^2 ≤ R*y 2 := by nlinarith
  have hXX : (y 4)^2 ≤ R*y 4 := by nlinarith
  have hBz : y 1*y 2 ≤ R*y 2 := mul_le_mul_of_nonneg_right hB' hz
  have hzB : y 2*y 1 ≤ R*y 1 := mul_le_mul_of_nonneg_right hz' hB
  have hzX : y 2*y 4 ≤ R*y 2 := by nlinarith [mul_le_mul_of_nonneg_left hX' hz]
  have hRA := mul_nonneg (by linarith : 0 ≤ R) hA
  have hRB := mul_nonneg (by linarith : 0 ≤ R) hB
  have hRz := mul_nonneg (by linarith : 0 ≤ R) hz
  have hRH := mul_nonneg (by linarith : 0 ≤ R) hH
  have hRX := mul_nonneg (by linarith : 0 ≤ R) hX
  fin_cases i
  · change -(30+10*R)*y 0 ≤ rateA r (y 0) (y 1) (y 2)
    have loss := mul_le_mul_of_nonneg_right (show r.p+r.alpha ≤ 4 by linarith [hr.p.2,hr.alpha.2]) hA
    have er := mul_le_mul_of_nonneg_right (show r.er ≤ 1 by linarith [hr.er.2]) (sq_nonneg (y 0))
    have q := mul_nonneg (mul_nonneg (by linarith [hr.q.1] : 0 ≤ r.q) hB) hz
    have ef := mul_nonneg (by linarith [hr.ef.1] : 0 ≤ r.ef) hB
    dsimp [rateA]
    nlinarith [hr.a.1]
  · change -(30+10*R)*y 1 ≤ rateB r (y 0) (y 1) (y 2)
    have q := mul_le_mul_of_nonneg_right (show r.q ≤ 2 by linarith [hr.q.2]) (mul_nonneg hz hB)
    have loss := mul_le_mul_of_nonneg_right (show r.beta+r.ef ≤ 3 by linarith [hr.beta.2,hr.ef.2]) hB
    have p := mul_nonneg (by linarith [hr.p.1] : 0 ≤ r.p) hA
    have er := mul_nonneg (by linarith [hr.er.1] : 0 ≤ r.er) (sq_nonneg (y 0))
    dsimp [rateB]
    nlinarith [hr.b.1]
  · change -(30+10*R)*y 2 ≤ rateZ r (y 0) (y 1) (y 2) (y 3) (y 4)
    have q := mul_le_mul_of_nonneg_right (show r.q ≤ 2 by linarith [hr.q.2]) (mul_nonneg hB hz)
    have u := mul_le_mul_of_nonneg_right (show r.u ≤ 17 by linarith [hr.u.2]) hz
    have v := mul_le_mul_of_nonneg_right (show r.v ≤ 3 by linarith [hr.v.2]) (sq_nonneg (y 2))
    have k := mul_le_mul_of_nonneg_right (show r.k ≤ 2 by linarith [hr.k.2]) (mul_nonneg hz hX)
    have p := mul_nonneg (by linarith [hr.p.1] : 0 ≤ r.p) hA
    have h := mul_nonneg (by linarith [hr.h1.1,hr.h2.1] : 0 ≤ r.h1+2*r.h2) hH
    dsimp [rateZ]
    nlinarith
  · change -(30+10*R)*y 3 ≤ rateH r (y 2) (y 3)
    have u := mul_nonneg (by linarith [hr.u.1] : 0 ≤ r.u) hz
    have v := mul_nonneg (by linarith [hr.v.1] : 0 ≤ r.v) (sq_nonneg (y 2))
    have loss := mul_le_mul_of_nonneg_right
      (show r.h1+r.h2+r.d ≤ 3 by linarith [hr.h1.2,hr.h2.2,hr.d.2]) hH
    dsimp [rateH]
    nlinarith
  · change -(30+10*R)*y 4 ≤ rateX r (y 2) (y 4)
    have k := mul_nonneg (by linarith [hr.k.1] : 0 ≤ r.k) (mul_nonneg hz hX)
    have mu := mul_le_mul_of_nonneg_right (show r.mu ≤ 1 by linarith [hr.mu.2]) hX
    have rho := mul_le_mul_of_nonneg_right (show r.rho ≤ 2 by linarith [hr.rho.2]) (sq_nonneg (y 4))
    dsimp [rateX]
    nlinarith

end RobustPermanence

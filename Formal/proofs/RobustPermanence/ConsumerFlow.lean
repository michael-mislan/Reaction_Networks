import proofs.RobustPermanence.ConsumerAbsorber
import proofs.CoreCouplingCAC.GlobalExistence
import proofs.CoreCouplingGlobal.ScalarBarrier

namespace RobustPermanence
open CoreCouplingCAC CoreCouplingGlobal

abbrev ConsumerVector := Fin 5 → ℝ

noncomputable def consumerField (e : ℝ) (y : ConsumerVector) : ConsumerVector :=
  ![fA (flagshipRates e) (y 0) (y 1) (y 2),
    fB (flagshipRates e) (y 0) (y 1) (y 2),
    fZ (flagshipRates e) (y 0) (y 1) (y 2) (y 3)-y 2*y 4,
    fH (flagshipRates e) (y 2) (y 3), y 4*(y 2-1/2-y 4)]

def consumerPositivePart (y : ConsumerVector) : ConsumerVector := fun i => max 0 (y i)

theorem consumerPositivePart_lipschitz : LipschitzWith 1 consumerPositivePart := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x y)).2
  intro i
  calc
    dist (consumerPositivePart x i) (consumerPositivePart y i) ≤ dist (x i) (y i) := by
      have hh := ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).const_max 0).dist_le_mul (x i) (y i)
      simpa only [consumerPositivePart,id_eq,NNReal.coe_one,one_mul] using hh
    _ ≤ dist x y := dist_le_pi_dist x y i

theorem consumerField_contDiff (e : ℝ) : ContDiff ℝ 1 (consumerField e) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [consumerField,fA,fB,fZ,fH,flagshipRates] <;> fun_prop

theorem consumer_extension_solution (e R : ℝ) (hR : 0 < R) (x₀ : ConsumerVector) :
    ∃ b : ConsumerVector → ℝ, ∃ X : ℝ → ConsumerVector,
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ (∀ x, ‖x‖ ≤ R → b x = 1) ∧
      X 0 = x₀ ∧ ∀ t, HasDerivAt X
        (b (consumerPositivePart (X t)) • consumerField e (consumerPositivePart (X t))) t := by
  let b : ContDiffBump (0 : ConsumerVector) := ⟨R,2*R,hR,by linarith⟩
  let f : ConsumerVector → ConsumerVector := fun x => b x • consumerField e x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (consumerField_contDiff e)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  have hlip : LipschitzWith K (fun x => f (consumerPositivePart x)) := by
    simpa only [mul_one] using hK.comp consumerPositivePart_lipschitz
  obtain ⟨X,hX0,hXd⟩ := bounded_lipschitz_global_solution (fun x => f (consumerPositivePart x)) K
    ⟨max C 0,le_max_right _ _⟩ hlip (fun x => (hC _).trans (le_max_left _ _)) x₀
  refine ⟨b,X,(fun _ => ⟨b.nonneg,b.le_one⟩),?_,hX0,hXd⟩
  intro x hx
  exact b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem consumer_boundary_nonneg (e : ℝ) (he : 0 ≤ e) (y : ConsumerVector)
    (hy : ∀ i, 0 ≤ y i) (i : Fin 5) (hi : y i = 0) : 0 ≤ consumerField e y i := by
  have h₀ := hy 0
  have h₁ := hy 1
  have h₂ := hy 2
  have h₃ := hy 3
  fin_cases i
  · change y 0 = 0 at hi
    change 0 ≤ 6-2*y 0+y 2*y 1+2*e*(y 1-(y 0)^2)
    rw [hi]
    nlinarith [mul_nonneg h₂ h₁,mul_nonneg he h₁]
  · change y 1 = 0 at hi
    change 0 ≤ 27+y 0-(1+y 2)*y 1-e*(y 1-(y 0)^2)
    rw [hi]
    nlinarith [mul_nonneg he (sq_nonneg (y 0))]
  · change y 2 = 0 at hi
    change 0 ≤ y 0-y 1*y 2-16*y 2-2*2*(y 2)^2+3*y 3-y 2*y 4
    rw [hi]
    linarith
  · change y 3 = 0 at hi
    change 0 ≤ 16*y 2+2*(y 2)^2-(2+1/10000)*y 3
    rw [hi]
    nlinarith
  · change y 4 = 0 at hi
    change 0 ≤ y 4*(y 2-1/2-y 4)
    rw [hi]
    norm_num

theorem consumer_extension_nonnegative (e : ℝ) (he : 0 ≤ e) (b : ConsumerVector → ℝ)
    (hb : ∀ x, 0 ≤ b x) (X : ℝ → ConsumerVector) (h0 : ∀ i, 0 ≤ X 0 i)
    (hd : ∀ t, HasDerivAt X (b (consumerPositivePart (X t)) • consumerField e (consumerPositivePart (X t))) t) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ X t i := by
  intro t ht i
  apply scalar_lower_barrier (fun t => X t i)
    (fun t => b (consumerPositivePart (X t))*consumerField e (consumerPositivePart (X t)) i) 0
    (fun t _ => (hasDerivAt_pi.1 (hd t)) i) (h0 i) ?_ t ht
  intro s _ hs
  apply mul_nonneg (hb _)
  apply consumer_boundary_nonneg e he _ (fun j => le_max_left 0 (X s j)) i
  exact max_eq_left hs

end RobustPermanence

import proofs.RAF1519.Refinement.Source
import proofs.ProductiveRecovery.WithdrawalRefill

namespace RAF1519.Refinement
noncomputable section

structure Intervention extends ProductiveRecovery.Intervention where
  lossD : ℝ
  lossD_lower : 49/50 ≤ lossD
  lossD_upper : lossD ≤ 1

def pulse (p : Intervention) (c : State) : State :=
  let s := ProductiveRecovery.pulse p.toIntervention (free c)
  ![s 0,s 1,s 2,s 3,s 4,s 5,p.q*p.lossD*c 6]

def Ready (theta : ℝ) (c : State) : Prop :=
  (∀ i, 0 ≤ c i) ∧ (159/160 ≤ materialA c ∧ materialA c ≤ 161/160) ∧
  (159/160 ≤ materialB c ∧ materialB c ≤ 161/160) ∧
  1/20 ≤ stock c ∧ c 6 ≤ (1101/1000)*theta

theorem free_nonneg (c : State) (hc : ∀ i, 0 ≤ c i) : ProductiveRecovery.Nonneg (free c) := by
  intro i
  fin_cases i <;> exact hc _

theorem free_pulse (p : Intervention) (c : State) :
    free (pulse p c) = ProductiveRecovery.pulse p.toIntervention (free c) := by
  funext i; fin_cases i <;> rfl

theorem pulse_nonnegative (p : Intervention) (c : State) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ pulse p c i := by
  have hs := ProductiveRecovery.pulse_nonnegative p.toIntervention (free c) (free_nonneg c hc)
  intro i
  fin_cases i
  all_goals first | exact hs _ | skip
  change 0 ≤ p.q*p.lossD*c 6
  exact mul_nonneg (mul_nonneg (by linarith [p.q_lower]) (by linarith [p.lossD_lower])) (hc 6)

theorem pulse_intermediate (p : Intervention) (c : State) (hc : ∀ i, 0 ≤ c i) :
    pulse p c 6 ≤ c 6 := by
  change p.q*p.lossD*c 6 ≤ c 6
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have hm := mul_le_mul_of_nonneg_left p.lossD_upper hq
  have hn := mul_le_mul_of_nonneg_right hm (hc 6)
  nlinarith [mul_le_mul_of_nonneg_right p.q_upper (hc 6),hc 6]

theorem pulse_stock (p : Intervention) (c : State) (hc : ∀ i, 0 ≤ c i)
    (hy : 1/20 ≤ stock c) : 49/4000 ≤ stock (pulse p c) := by
  have hh := ProductiveRecovery.pulse_catalyst p.toIntervention (free c) (free_nonneg c hc)
  change 49/4000 ≤ ProductiveRecovery.Y (free (pulse p c))
  rw [free_pulse]
  change 1/20 ≤ ProductiveRecovery.Y (free c) at hy
  linarith

theorem pulse_material (p : Intervention) (c : State) (hc : ∀ i, 0 ≤ c i)
    (ha : 159/160 ≤ materialA c ∧ materialA c ≤ 161/160)
    (hb : 159/160 ≤ materialB c ∧ materialB c ≤ 161/160) :
    (19/20 ≤ materialA (pulse p c) ∧ materialA (pulse p c) ≤ 11/10) ∧
    (19/20 ≤ materialB (pulse p c) ∧ materialB (pulse p c) ≤ 11/10) := by
  have hfree := free_nonneg c hc
  have h0 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 0
  have h1 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 1
  have h2 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 2
  have h3 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 3
  have h4 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 4
  have h5 := ProductiveRecovery.retained_bounds p.toIntervention (free c) hfree 5
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have h6L := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p.lossD_lower hq) (hc 6)
  have h6U := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left p.lossD_upper hq) (hc 6)
  have haL := mul_le_mul_of_nonneg_left ha.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have haU := mul_le_mul_of_nonneg_left ha.2 hq
  have hbL := mul_le_mul_of_nonneg_left hb.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have hbU := mul_le_mul_of_nonneg_left hb.2 hq
  simp [materialA,materialB,ProductiveRecovery.A,ProductiveRecovery.B,free] at haL haU hbL hbU
  simp only [materialA,materialB,free_pulse]
  norm_num [ProductiveRecovery.A,ProductiveRecovery.B,
    ProductiveRecovery.pulse,ProductiveRecovery.retained,free,pulse,Fin.ext_iff]
  change
    (19/20 <= p.q*p.loss 0*c 0+(1-p.q+p.eU)+p.q*p.loss 2*c 2+2*(p.q*p.loss 3*c 3)+2*(p.q*p.loss 4*c 4)+2*(p.q*p.loss 5*c 5)+p.q*p.lossD*c 6 ∧
      p.q*p.loss 0*c 0+(1-p.q+p.eU)+p.q*p.loss 2*c 2+2*(p.q*p.loss 3*c 3)+2*(p.q*p.loss 4*c 4)+2*(p.q*p.loss 5*c 5)+p.q*p.lossD*c 6 <= 11/10) ∧
    (19/20 <= p.q*p.loss 1*c 1+(1-p.q+p.eW)+p.q*p.loss 2*c 2+p.q*p.loss 3*c 3+2*(p.q*p.loss 4*c 4)+2*(p.q*p.loss 5*c 5)+p.q*p.lossD*c 6 ∧
      p.q*p.loss 1*c 1+(1-p.q+p.eW)+p.q*p.loss 2*c 2+p.q*p.loss 3*c 3+2*(p.q*p.loss 4*c 4)+2*(p.q*p.loss 5*c 5)+p.q*p.lossD*c 6 <= 11/10)
  simp [ProductiveRecovery.retained,free] at h0 h1 h2 h3 h4 h5
  constructor
  · constructor
    · linear_combination h0.1+h2.1+2*h3.1+2*h4.1+2*h5.1+h6L+haL+
        (209/8000)*p.q_upper+p.eU_lower
    · linear_combination h0.2+h2.2+2*h3.2+2*h4.2+2*h5.2+h6U+haU+
        (1/160)*p.q_upper+p.eU_upper
  · constructor
    · linear_combination h1.1+h2.1+h3.1+2*h4.1+2*h5.1+h6L+hbL+
        (209/8000)*p.q_upper+p.eW_lower
    · linear_combination h1.2+h2.2+h3.2+2*h4.2+2*h5.2+h6U+hbU+
        (1/160)*p.q_upper+p.eW_upper
end
end RAF1519.Refinement

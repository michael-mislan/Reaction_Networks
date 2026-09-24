import proofs.ProductiveRecovery.Source

namespace ProductiveRecovery
noncomputable section

structure Intervention where
  q : ℝ
  loss : State
  eU : ℝ
  eW : ℝ
  q_lower : 1/4 ≤ q
  q_upper : q ≤ 3/4
  loss_lower : ∀ i, 49/50 ≤ loss i
  loss_upper : ∀ i, loss i ≤ 1
  eU_lower : -(1/200) ≤ eU
  eU_upper : eU ≤ 1/200
  eW_lower : -(1/200) ≤ eW
  eW_upper : eW ≤ 1/200

def retained (p : Intervention) (c : State) : State := fun i => p.q*p.loss i*c i
def pulse (p : Intervention) (c : State) : State :=
  fun i => retained p c i + if i=0 then 1-p.q+p.eU else if i=1 then 1-p.q+p.eW else 0
def withdrawn (p : Intervention) (c : State) : State := fun i => (1-p.q)*c i
def lost (p : Intervention) (c : State) : State := fun i => p.q*(1-p.loss i)*c i

theorem removal_accounting (p : Intervention) (c : State) (i : Fin 6) :
    retained p c i + withdrawn p c i + lost p c i = c i := by
  dsimp [retained,withdrawn,lost]; ring

theorem food_feasible (p : Intervention) :
    49/200 ≤ 1-p.q+p.eU ∧ 1-p.q+p.eU ≤ 151/200 ∧
    49/200 ≤ 1-p.q+p.eW ∧ 1-p.q+p.eW ≤ 151/200 := by
  have := p.q_lower
  have := p.q_upper
  have := p.eU_lower
  have := p.eU_upper
  have := p.eW_lower
  have := p.eW_upper
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem retained_bounds (p : Intervention) (c : State) (hc : Nonneg c) (i : Fin 6) :
    p.q*(49/50)*c i ≤ retained p c i ∧ retained p c i ≤ p.q*c i := by
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  dsimp [retained]
  constructor
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (p.loss_lower i) hq) (hc i)
  · simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (p.loss_upper i) hq) (hc i)

theorem pulse_nonnegative (p : Intervention) (c : State) (hc : Nonneg c) : Nonneg (pulse p c) := by
  intro i
  have hr : 0 ≤ retained p c i := by
    dsimp [retained]
    exact mul_nonneg (mul_nonneg (by linarith [p.q_lower])
      (by linarith [p.loss_lower i])) (hc i)
  obtain ⟨hu, _, hw, _⟩ := food_feasible p
  dsimp [pulse]
  split_ifs <;> linarith

theorem pulse_material (p : Intervention) (c : State) (hc : Nonneg c)
    (ha : 9/10 ≤ A c ∧ A c ≤ 11/10) (hb : 9/10 ≤ B c ∧ B c ≤ 11/10) :
    (1813/2000 ≤ A (pulse p c) ∧ A (pulse p c) ≤ 27/25) ∧
    (1813/2000 ≤ B (pulse p c) ∧ B (pulse p c) ≤ 27/25) := by
  have h0 := retained_bounds p c hc 0
  have h1 := retained_bounds p c hc 1
  have h2 := retained_bounds p c hc 2
  have h3 := retained_bounds p c hc 3
  have h4 := retained_bounds p c hc 4
  have h5 := retained_bounds p c hc 5
  have hq : 0 ≤ p.q := by linarith [p.q_lower]
  have haL := mul_le_mul_of_nonneg_left ha.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have haU := mul_le_mul_of_nonneg_left ha.2 hq
  have hbL := mul_le_mul_of_nonneg_left hb.1 (mul_nonneg hq (by norm_num : (0:ℝ) ≤ 49/50))
  have hbU := mul_le_mul_of_nonneg_left hb.2 hq
  dsimp [A,B] at haL haU hbL hbU
  norm_num [A,B,pulse,Fin.ext_iff]
  constructor <;> constructor <;>
    nlinarith [p.q_upper,p.eU_lower,p.eU_upper,p.eW_lower,p.eW_upper]

theorem pulse_catalyst (p : Intervention) (c : State) (hc : Nonneg c) :
    (49/200)*Y c ≤ Y (pulse p c) := by
  have h2 := retained_bounds p c hc 2
  have h3 := retained_bounds p c hc 3
  have h4 := retained_bounds p c hc 4
  have h5 := retained_bounds p c hc 5
  have hy : 0 ≤ Y c := by
    dsimp [Y]
    linarith [hc 2,hc 3,hc 4,hc 5]
  have hq := mul_nonneg (sub_nonneg.mpr p.q_lower) hy
  dsimp [Y] at hq
  norm_num [Y,pulse,Fin.ext_iff]
  nlinarith

end
end ProductiveRecovery

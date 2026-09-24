import proofs.RAF1519.Reservoir.Scalar

namespace RAF1519.Reservoir
noncomputable section
open Set
open scoped BigOperators

abbrev Community (n : ℕ) := Fin 5 ⊕ Fin n → ℝ

def aggregate {n : ℕ} (x : Community n) : Fin 6 → ℝ :=
  ![x (.inl 0),x (.inl 1),x (.inl 2),x (.inl 3),x (.inl 4),∑ i, x (.inr i)]

def communityField {n : ℕ} (q : Fin n → ℝ) (x : Community n) : Community n :=
  Sum.elim (fun i => field (aggregate x) i.castSucc)
    (fun i => x (.inr i)*(x (.inl 4)*x (.inl 2)-1/2-x (.inr i)/q i))

def lift {n : ℕ} (q : Fin n → ℝ) (s : ℝ) : Community n :=
  Sum.elim (fun i => state s i.castSucc) (fun i => q i*s)

theorem aggregate_lift {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1) (s : ℝ) :
    aggregate (lift q s) = state s := by
  have hsum : (∑ i, q i*s) = s := by rw [← Finset.sum_mul,hq,one_mul]
  change ![precursor s,substrate s,resource s,catalyst s,reservoir s,∑ i, q i*s] =
    ![precursor s,substrate s,resource s,catalyst s,reservoir s,s]
  rw [hsum]

theorem lift_stationary {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1)
    (hpos : ∀ i, 0 < q i) (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40))
    (hf : field (state s) = 0) : communityField q (lift q s) = 0 := by
  have hr : reservoir s ≠ 0 := ne_of_gt (reservoir_positive s hs)
  have hR : reservoir s*resource s = 1/2+s := by unfold resource; field_simp
  funext i
  cases i with
  | inl i =>
    change field (aggregate (lift q s)) i.castSucc = 0
    rw [aggregate_lift q hq s,hf]
    rfl
  | inr i =>
    change q i*s*(reservoir s*resource s-1/2-q i*s/q i) = 0
    have hqi : q i ≠ 0 := ne_of_gt (hpos i)
    rw [hR]
    field_simp
    ring

theorem lift_positive {n : ℕ} (q : Fin n → ℝ) (hpos : ∀ i, 0 < q i)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) (3/40)) (hs' : 0 < s) :
    ∀ i, 0 < lift q s i := by
  intro i
  cases i with
  | inl i => exact state_positive s hs hs' i.castSucc
  | inr i => exact mul_pos (hpos i) hs'

theorem prescribed_composition {n : ℕ} (q : Fin n → ℝ) (hq : ∑ i, q i = 1)
    (s : ℝ) (hs : 0 < s) (i : Fin n) :
    lift q s (.inr i)/(∑ j, lift q s (.inr j)) = q i := by
  change q i*s/(∑ j, q j*s) = q i
  rw [← Finset.sum_mul,hq,one_mul,mul_div_cancel_right₀ _ (ne_of_gt hs)]

/-- Existence and prescribed composition only. Attraction is a separate obligation. -/
theorem two_stationary_communities {n : ℕ} (q : Fin n → ℝ)
    (hq : ∑ i, q i = 1) (hpos : ∀ i, 0 < q i) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ uptake a < uptake b ∧
      (∀ i, 0 < lift q a i) ∧ (∀ i, 0 < lift q b i) ∧
      communityField q (lift q a) = 0 ∧ communityField q (lift q b) = 0 ∧
      (∀ i, lift q a (.inr i)/(∑ j, lift q a (.inr j)) = q i) ∧
      (∀ i, lift q b (.inr i)/(∑ j, lift q b (.inr j)) = q i) := by
  obtain ⟨a,b,ha,hb,hab,hpa,hpb,hfa,hfb⟩ := two_positive_stationary_states
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := ha0.trans hab
  have haI : a ∈ Icc (0:ℝ) (3/40) := ⟨ha0.le,by linarith [ha.2]⟩
  have hbI : b ∈ Icc (0:ℝ) (3/40) := ⟨hb0.le,by linarith [hb.2]⟩
  refine ⟨a,b,ha0,hab,?_,lift_positive q hpos a haI ha0,
    lift_positive q hpos b hbI hb0,lift_stationary q hq hpos a haI hfa,
    lift_stationary q hq hpos b hbI hfb,prescribed_composition q hq a ha0,
    prescribed_composition q hq b hb0⟩
  unfold uptake
  nlinarith [mul_pos (sub_pos.mpr hab) (show 0 < a+b by linarith)]

end
end RAF1519.Reservoir

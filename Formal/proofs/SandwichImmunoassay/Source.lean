import Mathlib

namespace SandwichImmunoassay

/-- An occupancy satisfying finite-reagent mass balance at equilibrium. -/
structure Occupancy (x C K p : ℝ) : Prop where
  x_nonneg : 0 ≤ x
  total_pos : 0 < C
  kd_pos : 0 < K
  pos : 0 < p
  lt_one : p < 1
  balance : C = x * p + K * p / (1 - p)

theorem Occupancy.polynomial {x C K p : ℝ} (h : Occupancy x C K p) :
    C * (1-p) = x*p*(1-p)+K*p := by
  have hp : 1-p ≠ 0 := ne_of_gt (sub_pos.mpr h.lt_one)
  have := h.balance
  field_simp at this
  nlinarith

theorem Occupancy.bounds {x C K p : ℝ} (h : Occupancy x C K p) :
    C / (x+K+C) ≤ p ∧ p ≤ C / (x+K) := by
  have hx := h.x_nonneg
  have hc := h.total_pos
  have hk := h.kd_pos
  have hp := h.pos
  have hp1 := h.lt_one
  have hb := h.polynomial
  have xp : 0 ≤ x*p := mul_nonneg hx hp.le
  have free : 0 ≤ C-x*p := by
    rw [h.balance]
    have : 0 < 1-p := sub_pos.mpr hp1
    simp only [add_sub_cancel_left]
    positivity
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < x+K+C)).2
    nlinarith [mul_nonneg xp (sub_nonneg.mpr hp1.le)]
  · apply (le_div_iff₀ (by positivity : 0 < x+K)).2
    nlinarith [mul_nonneg hp.le free]

theorem Occupancy.unique {x C K p q : ℝ}
    (h : Occupancy x C K p) (j : Occupancy x C K q) : p=q := by
  have hp := h.polynomial
  have hq := j.polynomial
  have hx := h.x_nonneg
  have hk := h.kd_pos
  have pp := h.pos
  have qq := j.pos
  have p1 := h.lt_one
  have q1 := j.lt_one
  have hc := h.total_pos
  have hb := h.bounds.2
  have hb' : p*(x+K) ≤ C := (le_div_iff₀ (by positivity)).1 hb
  have coef : 0 < x+K+C-x*(p+q) := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr q1.le)]
  have prod : (p-q)*(x+K+C-x*(p+q))=0 := by nlinarith
  exact (mul_eq_zero.mp prod).resolve_right (ne_of_gt coef) |> sub_eq_zero.mp

structure Reaction (x C D K J p q : ℝ) : Prop where
  capture : Occupancy x C K p
  detector : Occupancy x D J q

theorem occupancy_exists {x C K : ℝ} (hx : 0 ≤ x) (hc : 0 < C) (hk : 0 < K) :
    ∃ p, Occupancy x C K p := by
  let f : ℝ → ℝ := fun p => (C-x*p)*(1-p)-K*p
  have hf : ContinuousOn f (Set.Icc 0 1) := by dsimp [f]; fun_prop
  have hz : (0:ℝ) ∈ Set.Icc (f 1) (f 0) := by dsimp [f]; constructor <;> nlinarith
  obtain ⟨p,hp,hf0⟩ := intermediate_value_Icc' (by norm_num : (0:ℝ) ≤ 1) hf hz
  have eqn : (C-x*p)*(1-p)-K*p = 0 := hf0
  have pp : 0 < p := by
    rcases hp with ⟨h0,h1⟩
    by_contra hn
    have : p=0 := by linarith
    subst p
    nlinarith
  have p1 : p < 1 := by
    rcases hp with ⟨h0,h1⟩
    by_contra hn
    have : p=1 := by linarith
    subst p
    nlinarith
  refine ⟨p,hx,hc,hk,pp,p1,?_⟩
  have hb : C-x*p = K*p/(1-p) :=
    (eq_div_iff (ne_of_gt (sub_pos.mpr p1))).2 (by nlinarith)
  linarith

theorem reaction_exists {x C D K J : ℝ} (hx : 0 ≤ x)
    (hc : 0<C) (hd : 0<D) (hk : 0<K) (hj : 0<J) :
    ∃ p q, Reaction x C D K J p q := by
  obtain ⟨p,hp⟩ := occupancy_exists hx hc hk
  obtain ⟨q,hq⟩ := occupancy_exists hx hd hj
  exact ⟨p,q,hp,hq⟩

theorem source_conservation (x p q : ℝ) :
    x*(1-p)*(1-q)+x*p*(1-q)+x*(1-p)*q+x*p*q=x := by ring

def signal (x p q : ℝ) : ℝ := x*p*q

theorem Reaction.signal_nonneg {x C D K J p q : ℝ}
    (h : Reaction x C D K J p q) : 0 ≤ signal x p q := by
  unfold signal
  exact mul_nonneg (mul_nonneg h.capture.x_nonneg h.capture.pos.le) h.detector.pos.le

theorem Reaction.signal_le_x {x C D K J p q : ℝ}
    (h : Reaction x C D K J p q) : signal x p q ≤ x := by
  have hp := h.capture.pos
  have hq := h.detector.pos
  have hp1 := h.capture.lt_one
  have hq1 := h.detector.lt_one
  have hx := h.capture.x_nonneg
  unfold signal
  calc
    x*p*q ≤ x*1*1 := mul_le_mul (mul_le_mul_of_nonneg_left hp1.le hx) hq1.le hq.le (by positivity)
    _ = x := by ring

theorem Reaction.envelopes {x C D K J p q : ℝ}
    (h : Reaction x C D K J p q) :
    C*D*x / ((x+K+C)*(x+J+D)) ≤ signal x p q ∧
    signal x p q ≤ C*D*x / ((x+K)*(x+J)) := by
  have hx := h.capture.x_nonneg
  have hc := h.capture.total_pos
  have hd := h.detector.total_pos
  have hk := h.capture.kd_pos
  have hj := h.detector.kd_pos
  have hp := h.capture.pos
  have hq := h.detector.pos
  have a := h.capture.bounds
  have b := h.detector.bounds
  constructor
  · have hh := mul_le_mul a.1 b.1 (by positivity : 0 ≤ D/(x+J+D)) hp.le
    have := mul_le_mul_of_nonneg_left hh hx
    dsimp [signal]
    convert this using 1 <;> field_simp
  · have hh := mul_le_mul a.2 b.2 hq.le (by positivity : 0 ≤ C/(x+K))
    have := mul_le_mul_of_nonneg_left hh hx
    dsimp [signal]
    convert this using 1 <;> field_simp

theorem source_endpoint_collision :
    Reaction (200/2499) 1 1 1 1 (49/100) (49/100) ∧
    Reaction (2499/50) 1 1 1 1 (1/51) (1/51) ∧
    signal (200/2499) (49/100) (49/100) = signal (2499/50) (1/51) (1/51) ∧
    (200/2499:ℝ) ≤ 1/10 ∧ (25:ℝ) ≤ 2499/50 ∧ (2499/50:ℝ) ≤ 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> constructor <;> norm_num
  · constructor <;> constructor <;> norm_num
  · norm_num [signal]
  · norm_num
  · norm_num
  · norm_num

end SandwichImmunoassay

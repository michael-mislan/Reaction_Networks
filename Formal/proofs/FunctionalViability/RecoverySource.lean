import Mathlib

namespace FunctionalViability
noncomputable section

/-- Two finite recovery stages. x is activation by the first deadline; y is
conditional qualifying progeny by the second deadline after activation.+The other recovery condition has complementary stage transitions. -/
def response (w x y : ℝ) : ℝ := w * (x*y) + (1-w)*((1-x)*(1-y))

def floor (d : ℝ) : ℝ := (1-d^2)/4

/-- Seven terminal source paths: inactive; condition 1 dormant/active/hit;
condition 2 dormant/active/hit. Weights are products of conditional transitions. -/
def pathWeight (p w x y : ℝ) : Fin 7 → ℝ :=
  ![1-p, p*w*(1-x), p*w*x*(1-y), p*w*x*y,
    p*(1-w)*x, p*(1-w)*(1-x)*y, p*(1-w)*(1-x)*(1-y)]

def negative : Fin 7 → Bool := ![true, true, true, false, true, true, false]

theorem source_normalized (p w x y : ℝ) :
    ∑ i, pathWeight p w x y i = 1 := by
  simp [pathWeight, Fin.sum_univ_succ]
  ring

theorem source_nonneg (p w x y : ℝ)
    (hp : 0 ≤ p ∧ p ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    ∀ i, 0 ≤ pathWeight p w x y i := by
  rcases hp with ⟨hp, hp'⟩
  rcases hw with ⟨hw, hw'⟩
  rcases hx with ⟨hx, hx'⟩
  rcases hy with ⟨hy, hy'⟩
  have hp1 : 0 ≤ 1-p := by linarith
  have hw1 : 0 ≤ 1-w := by linarith
  have hx1 : 0 ≤ 1-x := by linarith
  have hy1 : 0 ≤ 1-y := by linarith
  intro i
  fin_cases i
  · exact hp1
  · change 0 ≤ p*w*(1-x); positivity
  · change 0 ≤ p*w*x*(1-y); positivity
  · change 0 ≤ p*w*x*y; positivity
  · change 0 ≤ p*(1-w)*x; positivity
  · change 0 ≤ p*(1-w)*(1-x)*y; positivity
  · change 0 ≤ p*(1-w)*(1-x)*(1-y); positivity

theorem source_negative (p w x y : ℝ) :
    (∑ i, if negative i then pathWeight p w x y i else 0) =
      1-p*response w x y := by
  norm_num [negative, pathWeight, Fin.sum_univ_succ, response]
  ring

theorem alignment_identity (x y : ℝ) :
    response (1/2) x y = ((x+y-1)^2 + 1-(x-y)^2)/4 := by
  unfold response
  ring

theorem alignment_floor (x y d : ℝ) (h : |x-y| ≤ d) :
    floor d ≤ response (1/2) x y := by
  rw [alignment_identity]
  have hab := abs_le.mp h
  have hs : (x-y)^2 ≤ d^2 := by nlinarith [sq_nonneg (x-y+d), mul_nonneg (by linarith : 0 ≤ d-(x-y)) (by linarith : 0 ≤ d+(x-y))]
  unfold floor
  nlinarith [sq_nonneg (x+y-1)]

theorem response_nonneg (w x y : ℝ) (hw : 0 ≤ w ∧ w ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    0 ≤ response w x y := by
  rcases hw with ⟨hw, hw'⟩
  rcases hx with ⟨hx, hx'⟩
  rcases hy with ⟨hy, hy'⟩
  have hw1 : 0 ≤ 1-w := by linarith
  have hx1 : 0 ≤ 1-x := by linarith
  have hy1 : 0 ≤ 1-y := by linarith
  unfold response
  positivity

theorem response_le_one (w x y : ℝ) (hw : 0 ≤ w ∧ w ≤ 1)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) :
    response w x y ≤ 1 := by
  have hxy : x*y ≤ 1 := mul_le_one₀ hx.2 hy.1 hy.2
  have hxy' : (1-x)*(1-y) ≤ 1 := mul_le_one₀ (by linarith) (by linarith) (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hxy hw.1
  have h2 := mul_le_mul_of_nonneg_left hxy' (show 0 ≤ 1-w by linarith)
  unfold response
  nlinarith

theorem floor_nonneg (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) : 0 ≤ floor d := by
  unfold floor
  nlinarith [mul_nonneg hd.1 (show 0 ≤ 1-d by linarith)]

theorem floor_pos (d : ℝ) (hd : 0 ≤ d ∧ d < 1) : 0 < floor d := by
  unfold floor
  nlinarith [mul_pos (show 0 < 1-d by linarith) (show 0 < 1+d by linarith)]

theorem sharp_witness (w d : ℝ) :
    response w ((1+d)/2) ((1-d)/2) = floor d := by
  unfold response floor
  ring

theorem witness_admissible (d : ℝ) (hd : 0 ≤ d ∧ d ≤ 1) :
    (0 ≤ (1+d)/2 ∧ (1+d)/2 ≤ 1) ∧
    (0 ≤ (1-d)/2 ∧ (1-d)/2 ≤ 1) ∧
    |(1+d)/2-(1-d)/2| ≤ d := by
  have he : (1+d)/2-(1-d)/2 = d := by ring
  rw [he, abs_of_nonneg hd.1]
  constructor
  · constructor <;> linarith
  constructor
  · constructor <;> linarith
  exact le_rfl

theorem no_stage_alignment : response (1/2) 1 0 = 0 := by norm_num [response]

theorem single_condition_blind : response 1 0 0 = 0 ∧ response 0 1 1 = 0 := by
  norm_num [response]

end
end FunctionalViability

import proofs.FunctionalViability.RecoverySource

namespace FunctionalViability.Robust
noncomputable section

def recoveryFloor (c d : ℝ) : ℝ := max 0 (c^2-d^2)/4

def Admissible (c d x y a b : ℝ) : Prop :=
  (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧ (0 ≤ a ∧ a ≤ 1) ∧
  (0 ≤ b ∧ b ≤ 1) ∧ c ≤ x+a ∧ c ≤ y+b ∧ |x-y| ≤ d

theorem clipped_mismatch (x y c d : ℝ) (h : |x-y| ≤ d) :
    |min x c-min y c| ≤ d := by
  have h0 : 0 ≤ d := le_trans (abs_nonneg _) h
  rcases abs_le.mp h with ⟨hl, hu⟩
  rw [abs_le]
  by_cases hx : x ≤ c <;> by_cases hy : y ≤ c
  · simp only [min_eq_left hx, min_eq_left hy]; exact ⟨hl, hu⟩
  · rw [min_eq_left hx, min_eq_right (le_of_not_ge hy)]
    constructor <;> linarith
  · rw [min_eq_right (le_of_not_ge hx), min_eq_left hy]
    constructor <;> linarith
  · rw [min_eq_right (le_of_not_ge hx), min_eq_right (le_of_not_ge hy)]
    constructor <;> linarith

theorem coverage_bound (c d x y a b : ℝ) (hc : 0 ≤ c)
    (h : Admissible c d x y a b) : recoveryFloor c d ≤ (x*y+a*b)/2 := by
  rcases h with ⟨hx, hy, ha, hb, hca, hcb, hd⟩
  let X := min x c
  let Y := min y c
  have hX0 : 0 ≤ X := le_min hx.1 hc
  have hY0 : 0 ≤ Y := le_min hy.1 hc
  have hXx : X ≤ x := min_le_left _ _
  have hYy : Y ≤ y := min_le_left _ _
  have hXc : X ≤ c := min_le_right _ _
  have hYc : Y ≤ c := min_le_right _ _
  have hXa : c-X ≤ a := by
    dsimp [X]
    by_cases ht : x ≤ c
    · rw [min_eq_left ht]; linarith
    · rw [min_eq_right (le_of_not_ge ht)]; linarith [ha.1]
  have hYb : c-Y ≤ b := by
    dsimp [Y]
    by_cases ht : y ≤ c
    · rw [min_eq_left ht]; linarith
    · rw [min_eq_right (le_of_not_ge ht)]; linarith [hb.1]
  have hxy : X*Y ≤ x*y := mul_le_mul hXx hYy hY0 hx.1
  have hab : (c-X)*(c-Y) ≤ a*b :=
    mul_le_mul hXa hYb (by linarith) ha.1
  have hm := abs_le.mp (clipped_mismatch x y c d hd)
  change -d ≤ X-Y ∧ X-Y ≤ d at hm
  have hs : (X-Y)^2 ≤ d^2 := by
    nlinarith [mul_nonneg (show 0 ≤ d-(X-Y) by linarith [hm.2])
      (show 0 ≤ d+(X-Y) by linarith [hm.1])]
  have hlow : c^2-d^2 ≤ 2*(x*y+a*b) := by
    nlinarith [sq_nonneg (X+Y-c)]
  have hn : 0 ≤ x*y+a*b := add_nonneg (mul_nonneg hx.1 hy.1) (mul_nonneg ha.1 hb.1)
  unfold recoveryFloor
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<4)).mpr
  apply max_le
  · linarith
  · linarith

theorem floor_nonnegative (c d : ℝ) : 0 ≤ recoveryFloor c d := by
  exact div_nonneg (le_max_left _ _) (by norm_num)

theorem sharp_witness (c d : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d) :
    ∃ x y a b, Admissible c d x y a b ∧
      x*y = recoveryFloor c d ∧ a*b = recoveryFloor c d := by
  by_cases hdc : d ≤ c
  · have hsq : 0 ≤ c^2-d^2 := by
      nlinarith [mul_nonneg (show 0 ≤ c-d by linarith) (show 0 ≤ c+d by linarith)]
    have hf : recoveryFloor c d = (c^2-d^2)/4 := by
      simp [recoveryFloor, max_eq_right hsq]
    refine ⟨(c+d)/2, (c-d)/2, (c-d)/2, (c+d)/2, ?_, ?_, ?_⟩
    · unfold Admissible
      have he : (c+d)/2-(c-d)/2 = d := by ring
      rw [he, abs_of_nonneg hd]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
        ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
        by linarith, by linarith, le_rfl⟩
    · rw [hf]; ring
    · rw [hf]; ring
  · have hcd : c ≤ d := le_of_not_ge hdc
    have hsq : c^2-d^2 ≤ 0 := by
      nlinarith [mul_nonneg (show 0 ≤ d-c by linarith) (show 0 ≤ d+c by linarith)]
    refine ⟨c, 0, 0, c, ?_, ?_, ?_⟩
    · simpa [Admissible, abs_of_nonneg hc.1] using And.intro hc (And.intro hc hcd)
    · simp [recoveryFloor, max_eq_left hsq]
    · simp [recoveryFloor, max_eq_left hsq]

theorem minimax (c d : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d) :
    (∀ x y a b, Admissible c d x y a b → recoveryFloor c d ≤ (x*y+a*b)/2) ∧
    (∀ w : ℝ, ∃ x y a b, Admissible c d x y a b ∧
      w*(x*y)+(1-w)*(a*b)=recoveryFloor c d) := by
  refine ⟨fun x y a b h => coverage_bound c d x y a b hc.1 h, ?_⟩
  intro w
  obtain ⟨x,y,a,b,h,hu,hv⟩ := sharp_witness c d hc hd
  refine ⟨x,y,a,b,h,?_⟩
  rw [hu,hv]; ring

theorem positive_iff (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 < recoveryFloor c d ↔ d < c := by
  unfold recoveryFloor
  rw [div_pos_iff_of_pos_right (by norm_num : (0:ℝ)<4), lt_max_iff]
  constructor
  · intro h
    rcases h with h | h
    · linarith
    · by_contra hdc
      have hcd : c ≤ d := le_of_not_gt hdc
      nlinarith [mul_nonneg (show 0 ≤ c+d by linarith) (show 0 ≤ d-c by linarith)]
  · intro h
    right
    nlinarith [mul_pos (show 0 < c-d by linarith) (show 0 < c+d by linarith)]

theorem approximate_complementarity (x y a b eps d : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (he : 0 ≤ eps ∧ eps ≤ 1) (hm : |x-y| ≤ d)
    (hea : |a-(1-x)| ≤ eps) (heb : |b-(1-y)| ≤ eps) :
    recoveryFloor (1-eps) d ≤ (x*y+a*b)/2 := by
  have h1 := (abs_le.mp hea).1
  have h2 := (abs_le.mp heb).1
  exact coverage_bound _ _ _ _ _ _ (by linarith) ⟨hx,hy,ha,hb,by linarith,by linarith,hm⟩

end
end FunctionalViability.Robust

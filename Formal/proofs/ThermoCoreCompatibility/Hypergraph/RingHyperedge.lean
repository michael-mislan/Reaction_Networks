import Mathlib

namespace ThermoCoreCompatibility.Hypergraph.Ring

def Productive (x y : ℝ) : Prop := x-y < 2*(y-x^2) ∧ y-x^2 < x-y

theorem productive_decreases {x y : ℝ} (h : Productive x y) : y < x := by
  obtain ⟨h₁,h₂⟩ := h
  linarith

theorem full_incompatible (n : ℕ) [NeZero n] :
    ¬ ∃ x : ZMod n → ℝ, ∀ i, Productive (x i) (x (i+1)) := by
  rintro ⟨x,hx⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  exact (not_lt_of_ge (hi (i+1) (Finset.mem_univ _))) (productive_decreases (hx i))

noncomputable def epsilon {n : ℕ} (j i : ZMod n) : ℝ := (1/20)*(5/8)^((j-i).val)

theorem epsilon_bounds {n : ℕ} (j i : ZMod n) :
    0 < epsilon j i ∧ epsilon j i ≤ 1/20 := by
  constructor
  · unfold epsilon
    positivity
  · have hp := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 5/8)
      (by norm_num : (5/8 : ℝ) ≤ 1) (n := (j-i).val)
    unfold epsilon
    linarith

theorem epsilon_step {n : ℕ} [NeZero n] (hn : 2 ≤ n) (j i : ZMod n) (hi : i ≠ j) :
    epsilon j (i+1) = (8/5)*epsilon j i := by
  have hd : j-i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
  have hv : 0 < (j-i).val := Nat.pos_of_ne_zero ((ZMod.val_eq_zero _).not.mpr hd)
  have hone : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  have hs : (j-(i+1)).val = (j-i).val-1 := by
    have he : j-(i+1) = (j-i)-1 := by ring
    rw [he,ZMod.val_sub (by omega),hone]
  have hv' : (j-i).val = ((j-i).val-1)+1 := by omega
  unfold epsilon
  rw [hs]
  conv_rhs => rw [hv',pow_succ]
  ring

theorem local_deletion {e : ℝ} (he : 0 < e) (hu : e ≤ 1/20) :
    Productive (1-e) (1-(8/5)*e) := by
  unfold Productive
  have hh : 0 < e*(1/10-e) := mul_pos he (by linarith)
  constructor <;> nlinarith [sq_nonneg e]

/-- Every deleted edge has a rational formula for one common physical state.
The same box is retained, including the omitted core's species. -/
theorem deletion_witness {n : ℕ} [NeZero n] (hn : 2 ≤ n) (j : ZMod n) :
    ∃ x : ZMod n → ℝ, (∀ i, 9/10 ≤ x i ∧ x i ≤ 1) ∧
      ∀ i, i ≠ j → Productive (x i) (x (i+1)) := by
  refine ⟨fun i => 1-epsilon j i,?_,?_⟩
  · intro i
    obtain ⟨he,hu⟩ := epsilon_bounds j i
    constructor <;> linarith
  · intro i hi
    dsimp only
    rw [epsilon_step hn j i hi]
    exact local_deletion (epsilon_bounds j i).1 (epsilon_bounds j i).2

end ThermoCoreCompatibility.Hypergraph.Ring

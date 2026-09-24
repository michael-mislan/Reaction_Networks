import Mathlib

namespace CoreCouplingGlobal
open Set

/-- A bounded derivative supplies a bounded divided difference in either orientation. -/
theorem bounded_secant (f d : ℝ → ℝ) (x y lo hi : ℝ) (hlh : lo ≤ hi)
    (hf : ∀ t ∈ uIcc x y, HasDerivAt f (d t) t)
    (hd : ∀ t ∈ uIcc x y, lo ≤ d t ∧ d t ≤ hi) :
    ∃ m, lo ≤ m ∧ m ≤ hi ∧ f y-f x = m*(y-x) := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hu : uIcc x y = Icc x y := uIcc_of_le (le_of_lt hxy)
    rw [hu] at hf hd
    obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f d hxy
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => hf t ⟨le_of_lt ht.1,le_of_lt ht.2⟩)
    exact ⟨d t,(hd t ⟨le_of_lt ht.1,le_of_lt ht.2⟩).1,
      (hd t ⟨le_of_lt ht.1,le_of_lt ht.2⟩).2,
      (eq_div_iff (by linarith : y-x ≠ 0)).1 heq |>.symm⟩
  · subst y
    exact ⟨lo,le_rfl,hlh,by ring⟩
  · have hu : uIcc x y = Icc y x := uIcc_of_ge (le_of_lt hxy)
    rw [hu] at hf hd
    obtain ⟨t,ht,heq⟩ := exists_hasDerivAt_eq_slope f d hxy
      (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht => hf t ⟨le_of_lt ht.1,le_of_lt ht.2⟩)
    refine ⟨d t,(hd t ⟨le_of_lt ht.1,le_of_lt ht.2⟩).1,
      (hd t ⟨le_of_lt ht.1,le_of_lt ht.2⟩).2,?_⟩
    have heq' := (eq_div_iff (by linarith : x-y ≠ 0)).1 heq
    nlinarith only [heq']

noncomputable def responseLog (z : ℝ) : ℝ := Real.log (z+1)-Real.log (z+2)

theorem responseLog_hasDerivAt (z : ℝ) (hz : -1 < z) :
    HasDerivAt responseLog (1/((z+1)*(z+2))) z := by
  have h₁ : z+1 ≠ 0 := by linarith
  have h₂ : z+2 ≠ 0 := by linarith
  convert (((hasDerivAt_id z).add_const 1).log h₁).sub
    (((hasDerivAt_id z).add_const 2).log h₂) using 1
  dsimp
  field_simp
  ring

theorem responseLog_secant (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 12)
    (hy : 0 ≤ y) (hy' : y ≤ 12) :
    ∃ m, 1/182 ≤ m ∧ m ≤ 1/2 ∧ responseLog y-responseLog x = m*(y-x) := by
  apply bounded_secant responseLog (fun t => 1/((t+1)*(t+2))) x y (1/182) (1/2)
    (by norm_num)
  · intro t ht
    have ht0 : 0 ≤ t := le_trans (le_min hx hy) ht.1
    exact responseLog_hasDerivAt t (by linarith)
  · intro t ht
    have ht0 : 0 ≤ t := le_trans (le_min hx hy) ht.1
    have ht12 : t ≤ 12 := le_trans ht.2 (max_le hx' hy')
    have hp : 0 < (t+1)*(t+2) := by positivity
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith [sq_nonneg (t-12)]
    · apply (div_le_iff₀ hp).2
      nlinarith [sq_nonneg t]

noncomputable def forkGradientPrimitive (B c z : ℝ) : ℝ :=
  (Real.log (z+2)-c*responseLog z)/B

theorem forkGradientPrimitive_hasDerivAt (B c z : ℝ) (hB : B ≠ 0) (hz : -1 < z) :
    HasDerivAt (forkGradientPrimitive B c)
      ((1-c/(z+1))/(B*(z+2))) z := by
  have h₁ : z+1 ≠ 0 := by linarith
  have h₂ : z+2 ≠ 0 := by linarith
  convert ((((hasDerivAt_id z).add_const 2).log h₂).sub
    ((responseLog_hasDerivAt z hz).const_mul c)).div_const B using 1
  dsimp
  field_simp

theorem fork_gradient_coefficient (B c t : ℝ)
    (ht : 13/17 ≤ t+1)
    (hl : 4 ≤ B*(t+2)) (hu : B*(t+2) ≤ 476)
    (hc : -(1/500) ≤ c) (hc' : c ≤ 1/500) :
    1/500 ≤ (1-c/(t+1))/(B*(t+2)) ∧
    (1-c/(t+1))/(B*(t+2)) ≤ 13/50 := by
  have ht0 : 0 < t+1 := by linarith
  have hp : 0 < B*(t+2) := by linarith
  have hcl : -(1/100:ℝ) ≤ c/(t+1) := (le_div_iff₀ ht0).2 (by linarith)
  have hcu : c/(t+1) ≤ (1/100:ℝ) := (div_le_iff₀ ht0).2 (by linarith)
  constructor
  · apply (le_div_iff₀ hp).2
    linarith
  · apply (div_le_iff₀ hp).2
    linarith

theorem fork_gradient_secant (B c z : ℝ) (hB : 2 ≤ B) (hB' : B ≤ 34)
    (hz : 0 ≤ z) (hz' : z ≤ 12) (hc : -(1/500) ≤ c) (hc' : c ≤ 1/500) :
    ∃ m, 1/500 ≤ m ∧ m ≤ 13/50 ∧
      (Real.log (z+2)-c*responseLog z)-
      (Real.log (60/B)-c*responseLog (60/B-2)) = -m*(60-(2+z)*B) := by
  have hB0 : 0 < B := by linarith
  have hb : B*(60/B-2+2) = 60 := by field_simp; ring
  have hb1 : 13/17 ≤ 60/B-2+1 := by
    have hh : (30/17:ℝ) ≤ 60/B := (le_div_iff₀ hB0).2 (by linarith)
    linarith
  have hz1 : 13/17 ≤ z+1 := by linarith
  have hzl : 4 ≤ B*(z+2) := by nlinarith
  have hzu : B*(z+2) ≤ 476 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 34-B) (by linarith : 0 ≤ 12-z)]
  have segment : ∀ t ∈ uIcc (60/B-2) z,
      13/17 ≤ t+1 ∧ 4 ≤ B*(t+2) ∧ B*(t+2) ≤ 476 := by
    intro t ht
    rcases (mem_uIcc.mp ht) with ht | ht
    · exact ⟨by linarith, by nlinarith, by nlinarith⟩
    · exact ⟨by linarith, by nlinarith, by nlinarith⟩
  obtain ⟨m,hml,hmu,hm⟩ := bounded_secant (forkGradientPrimitive B c)
    (fun t => (1-c/(t+1))/(B*(t+2))) (60/B-2) z (1/500) (13/50)
    (by norm_num)
    (fun t ht => forkGradientPrimitive_hasDerivAt B c t (ne_of_gt hB0)
      (by have hh := (segment t ht).1; linarith))
    (fun t ht => fork_gradient_coefficient B c t (segment t ht).1
      (segment t ht).2.1 (segment t ht).2.2 hc hc')
  refine ⟨m,hml,hmu,?_⟩
  dsimp [forkGradientPrimitive] at hm
  have heq : 60/B-2+2 = 60/B := by ring
  rw [heq] at hm
  have hmB := congrArg (fun x : ℝ => x*B) hm
  field_simp at hmB ⊢
  nlinarith only [hmB]

end CoreCouplingGlobal

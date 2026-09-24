import Mathlib.Tactic

namespace SmallResidentCompositionCopying

def Low (x y : ℕ) : Prop :=
  6 ≤ x ∧ x ≤ 106 ∧ y ≤ 8 ∧ 100*y ≤ 3*(x+y)

def High (x y : ℕ) : Prop :=
  371 ≤ x ∧ x ≤ 742 ∧ 6 ≤ y ∧ y ≤ 132 ∧ x+y ≤ 20*y

def Region (b : Bool) (x y : ℕ) : Prop := if b then High x y else Low x y

def encode (b : Bool) : ℕ × ℕ := if b then (530,53) else (53,0)

theorem encode_mem (b : Bool) : Region b (encode b).1 (encode b).2 := by
  cases b <;> norm_num [Region, encode, Low, High]

theorem resident_bounds (b : Bool) (x y : ℕ) (h : Region b x y) :
    6 ≤ x+y ∧ x+y ≤ 874 := by
  cases b <;> simp only [Region, Bool.false_eq_true, if_false, if_true] at h
  · rcases h with ⟨_,_,_,_⟩; omega
  · rcases h with ⟨_,_,_,_,_⟩; omega

theorem two_module_budget (b c : Bool) (x y u v : ℕ)
    (h : Region b x y) (k : Region c u v) : x+y+u+v ≤ 1748 := by
  have := (resident_bounds b x y h).2
  have := (resident_bounds c u v k).2
  omega

theorem distinct_labels_disjoint (x y : ℕ) : ¬ (Low x y ∧ High x y) := by
  rintro ⟨⟨_,_,_,_⟩,⟨_,_,_,_,_⟩⟩
  omega

/-- Homogeneous normalized coordinates: a module carrying at least 3/440
of the total mass separates low and high labels by a fixed L1 gap. -/
theorem normalized_local_separation (x y u v : ℝ)
    (hlo : 100*y ≤ 3*(x+y)) (hhi : u+v ≤ 20*v)
    (hmlo : (3:ℝ)/440 ≤ x+y) :
    (3:ℝ)/22000 ≤ |u-x| + |v-y| := by
  have ha := le_abs_self (v-y)
  have hb := neg_le_abs (u-x)
  have hc := abs_nonneg (v-y)
  have hd := abs_nonneg (u-x)
  linarith

theorem normalized_readout_low (x y : ℝ)
    (h : 100*y ≤ 3*(x+y)) (hm : (3:ℝ)/440 ≤ x+y) :
    y-(x+y)/25 ≤ -(3:ℝ)/44000 := by linarith

theorem normalized_readout_high (x y : ℝ)
    (h : x+y ≤ 20*y) (hm : (3:ℝ)/440 ≤ x+y) :
    (3:ℝ)/44000 ≤ y-(x+y)/25 := by linarith

end SmallResidentCompositionCopying

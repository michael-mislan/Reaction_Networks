import Mathlib
namespace PhenotypeMemory
def beneficial (x y : ℕ × ℕ) : Prop := x.1 ≤ y.1 ∧ y.2 ≤ x.2
theorem beneficial_trans {x y z : ℕ × ℕ} (h : beneficial x y)
    (k : beneficial y z) : beneficial x z := ⟨h.1.trans k.1, k.2.trans h.2⟩
/-- Equal activating coordinate: fewer repressors increase writing. The
same algebra, with roles reversed, handles equal repressive coordinate. -/
theorem equal_coordinate_write (N a r r' c : ℝ) (hr : r' ≤ r) (hc : 0 ≤ c) :
    (N-a-r)*c ≤ (N-a-r')*c := by nlinarith
theorem equal_coordinate_erase (a e h r r' : ℝ) (ha : 0 ≤ a)
    (hh : 0 ≤ h) (hr : r' ≤ r) : a*(e+h*r') ≤ a*(e+h*r) := by
  have := mul_nonneg ha (mul_nonneg hh (sub_nonneg.mpr hr))
  nlinarith
theorem ordered_allocation (a a' r r' i i' j j' : ℕ)
    (ha : i ≤ i') (hr : j' ≤ j) (hA : a-i ≤ a'-i')
    (hR : r'-j' ≤ r-j) : beneficial (i,j) (i',j') ∧
      beneficial (a-i,r-j) (a'-i',r'-j') := ⟨⟨ha,hr⟩,⟨hA,hR⟩⟩
end PhenotypeMemory

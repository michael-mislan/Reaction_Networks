import proofs.FiniteReservoir.FiniteModel

namespace FiniteReservoir
noncomputable section

def pureParameters (R : ℕ) (hR : 0 < R) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) : Parameters R where
  capacity := R
  capacity_pos := by exact_mod_cast hR
  release := r
  release_lower := hr
  release_upper := hr'
  cleavage := d
  cleavage_nonneg := hd
  inventory_bound := by
    have h := mul_le_mul_of_nonneg_right hd' (Nat.cast_nonneg (α:=ℝ) R)
    linarith

def loadedParameters (R : ℕ) (hR : 0 < R) (r : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) : Parameters (2*R) where
  capacity := R
  capacity_pos := by exact_mod_cast hR
  release := r
  release_lower := hr
  release_upper := hr'
  cleavage := 1/50
  cleavage_nonneg := by norm_num
  inventory_bound := by push_cast; linarith

def pureFuel (R : ℕ) : FuelState R := ⟨R,by omega⟩
def loadedFuel (R : ℕ) : FuelState (2*R) := ⟨R,by omega⟩

theorem pure_bath (R : ℕ) : bathOf (pureFuel R)=⟨R,0⟩ := by
  simp [bathOf,pureFuel]

theorem loaded_bath (R : ℕ) : bathOf (loadedFuel R)=⟨R,R⟩ := by
  simp only [bathOf,loadedFuel]
  congr 1
  omega

/-- The local coefficient assumptions hold for every possible return in Candidate A. -/
theorem pure_local_hypotheses (R : ℕ) (hR : 0 < R) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (fuel : FuelState R) :
    RateBox (alpha (bathOf fuel) d R) (beta (bathOf fuel) d R) :=
  parameters_box (pureParameters R hR r d hr hr' hd hd') fuel

theorem loaded_local_hypotheses (R : ℕ) (hR : 0 < R) (r : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (fuel : FuelState (2*R)) :
    RateBox (alpha (bathOf fuel) (1/50) R) (beta (bathOf fuel) (1/50) R) :=
  parameters_box (loadedParameters R hR r hr hr') fuel

end
end FiniteReservoir

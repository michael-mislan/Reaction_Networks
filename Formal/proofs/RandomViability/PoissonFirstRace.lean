import proofs.RandomViability.FirstRace

namespace RandomViability
open Classical FiniteCopy
noncomputable section

theorem poisson_power_hasSum (t r : NNReal) :
    HasSum (fun n : ℕ => poissonWeight t n*(r : ℝ)^n) (Real.exp (((r : ℝ)-1)*t)) := by
  simpa only [poissonWeight_tilt, mul_one] using
    (poissonWeight_sum (r*t)).mul_left (Real.exp (((r : ℝ)-1)*t))

namespace FiniteLabeledKernel
variable {α β : Type*} [Fintype β]

theorem firstRace_poisson_lower (K : FiniteLabeledKernel α β) (marked target : β → Prop)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1)
    (htarget : ∀ x, a ≤ ∑ z, if marked z ∧ target z then K.prob x z else 0)
    (hmarked : ∀ x, (∑ z, if marked z then K.prob x z else 0) ≤ b)
    (t : NNReal) (x : α) :
    a/b*(1-Real.exp (-b*t)) ≤ K.poissonEventMass t x (firstRace marked target) := by
  let r : NNReal := ⟨1-b, by linarith⟩
  have hr : (r : ℝ) = 1-b := rfl
  have he : ((r : ℝ)-1)*t = -b*t := by rw [hr]; ring
  have hp := poisson_power_hasSum t r
  rw [he] at hp
  rw [hr] at hp
  have hs : HasSum (fun n : ℕ => poissonWeight t n*(a/b*(1-(1-b)^n)))
      (a/b*(1-Real.exp (-b*t))) := by
    have hh := ((poissonWeight_sum t).sub hp).mul_left (a/b)
    convert hh using 1
    funext n
    dsimp [r]
    ring
  have hh := Summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left
      (K.firstRace_mass_lower marked target a b ha hb hb1 htarget hmarked n x)
      (poissonWeight_nonneg t n)) hs.summable
    (K.poissonEventMass_summable t x (firstRace marked target))
  rw [hs.tsum_eq] at hh
  exact hh

end FiniteLabeledKernel
end
end RandomViability

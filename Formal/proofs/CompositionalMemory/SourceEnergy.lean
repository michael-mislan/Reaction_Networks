import proofs.CompositionalMemory.IncrementBounds

namespace CompositionalMemory
open FiniteCopy

/-- Primitive local quadratic geometry shared by both source types. -/
structure EnergyData where
  energy : Point → ℝ
  pair : Point → Point → ℝ
  nonneg : ∀ x, 0 ≤ energy x
  upper : ∀ x, energy x ≤ 42*normSq x
  increment : ∀ y v, energy (fun a => y a+v a)-energy y = 2*pair y v+energy v
  pair_square : ∀ y v, (pair y v)^2 ≤ 1764*normSq y*normSq v

noncomputable def lowEnergyData : EnergyData where
  energy := lowEnergy
  pair := lowPair
  nonneg := fun x => by linarith only [lowEnergy_lower x,normSq_nonneg x]
  upper := fun x => by linarith only [lowEnergy_upper x,normSq_nonneg x]
  increment := fun y v => by unfold lowEnergy lowPair; ring
  pair_square := low_pair_squared_bound

noncomputable def highEnergyData : EnergyData where
  energy := highEnergy
  pair := highPair
  nonneg := fun x => by linarith only [highEnergy_lower x,normSq_nonneg x]
  upper := fun x => by simpa using highEnergy_upper x
  increment := fun y v => by unfold highEnergy highPair; ring
  pair_square := high_pair_squared_bound

theorem energy_increment_bound (E : EnergyData) (y v : Point) (r d : ℝ)
    (hr : 0 ≤ r) (hd : 0 ≤ d) (hy : normSq y = r^2) (hv : normSq v ≤ d^2) :
    |E.energy (fun a => y a+v a)-E.energy y| ≤ 84*r*d+42*d^2 := by
  rw [E.increment]
  have hp := E.pair_square y v
  rw [hy] at hp
  have hm := mul_le_mul_of_nonneg_left hv (show 0 ≤ 1764*r^2 by positivity)
  exact quadratic_increment_absolute (E.pair y v) (E.energy v) r d hr hd
    (hp.trans hm) (E.nonneg v) ((E.upper v).trans (by linarith only [hv]))

theorem normSq_div (x : Point) (m : ℝ) :
    normSq (fun a => x a/m) = normSq x/m^2 := by
  unfold normSq
  ring

theorem normSq_neg (x : Point) : normSq (fun a => -x a) = normSq x := by
  unfold normSq
  ring

noncomputable def localMembraneJump {k : ℕ} (m : ℝ) (i j : Fin k) (x : Point) : Point :=
  fun a => -(x a + if j=i then (if a=2 then (k : ℝ) else 0) else 0)/(m+1)

theorem local_membrane_jump_norm {k : ℕ} (m : ℝ)
    (i j : Fin k) (x : Point) (hx : normSq x ≤ 4900) (hxz : x 2 ≤ 70) :
    normSq (localMembraneJump m i j x) ≤
      ((70+if j=i then (k : ℝ) else 0)/(m+1))^2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold localMembraneJump
  rw [normSq_div,normSq_neg]
  rw [div_pow]
  by_cases h : j=i
  · simp only [h,ite_true]
    exact div_le_div_of_nonneg_right (consuming_vector_norm x k hk0 hx hxz) (sq_nonneg _)
  · simp only [h,ite_false,add_zero]
    exact div_le_div_of_nonneg_right (by norm_num at hx ⊢; exact hx) (sq_nonneg _)

end CompositionalMemory

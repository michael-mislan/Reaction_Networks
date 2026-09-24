import proofs.ThermoCoreCompatibility.MultiInterface.WeightedPair

namespace ThermoCoreCompatibility.BeyondJunction

open MultiInterface

theorem productive_min (w : Factors) {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (h : w.Productive x y) (h' : w.Productive x' y') :
    w.Productive (min x x') (min y y') := by
  rw [w.productive_iff] at h h' ⊢
  have hm : 0 ≤ min x x' := le_min hx hx'
  constructor
  · exact lt_min
      (lt_of_le_of_lt (w.lower_strictMono.monotoneOn hm hx (min_le_left _ _)) h.1)
      (lt_of_le_of_lt (w.lower_strictMono.monotoneOn hm hx' (min_le_right _ _)) h'.1)
  · rcases le_total x x' with hxx | hxx
    · rw [min_eq_left hxx]
      exact lt_of_le_of_lt (min_le_left _ _) h.2
    · rw [min_eq_right hxx]
      exact lt_of_le_of_lt (min_le_right _ _) h'.2

theorem productive_max (w : Factors) {x y x' y' : ℝ}
    (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (h : w.Productive x y) (h' : w.Productive x' y') :
    w.Productive (max x x') (max y y') := by
  rw [w.productive_iff] at h h' ⊢
  have hm : 0 ≤ max x x' := le_trans hx (le_max_left _ _)
  constructor
  · rcases le_total x x' with hxx | hxx
    · rw [max_eq_right hxx]
      exact lt_of_lt_of_le h'.1 (le_max_right _ _)
    · rw [max_eq_left hxx]
      exact lt_of_lt_of_le h.1 (le_max_left _ _)
  · exact max_lt
      (lt_of_lt_of_le h.2 (w.upper_strictMono.monotoneOn hx hm (le_max_left _ _)))
      (lt_of_lt_of_le h'.2 (w.upper_strictMono.monotoneOn hx' hm (le_max_right _ _)))

def BoxedProductive {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi z : V → ℝ) : Prop :=
  (∀ v, lo v ≤ z v ∧ z v ≤ hi v) ∧
    ∀ e, (w e).Productive (z (src e)) (z (dst e))

theorem boxed_min {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi z z' : V → ℝ) (hlo : ∀ v, 0 ≤ lo v)
    (h : BoxedProductive src dst w lo hi z)
    (h' : BoxedProductive src dst w lo hi z') :
    BoxedProductive src dst w lo hi (fun v => min (z v) (z' v)) := by
  constructor
  · intro v
    exact ⟨le_min (h.1 v).1 (h'.1 v).1,
      le_trans (min_le_left _ _) (h.1 v).2⟩
  · intro e
    exact productive_min (w e) (le_trans (hlo _) (h.1 _).1)
      (le_trans (hlo _) (h'.1 _).1) (h.2 e) (h'.2 e)

theorem boxed_max {V E : Type*} (src dst : E → V) (w : E → Factors)
    (lo hi z z' : V → ℝ) (hlo : ∀ v, 0 ≤ lo v)
    (h : BoxedProductive src dst w lo hi z)
    (h' : BoxedProductive src dst w lo hi z') :
    BoxedProductive src dst w lo hi (fun v => max (z v) (z' v)) := by
  constructor
  · intro v
    exact ⟨le_trans (h.1 v).1 (le_max_left _ _), max_le (h.1 v).2 (h'.1 v).2⟩
  · intro e
    exact productive_max (w e) (le_trans (hlo _) (h.1 _).1)
      (le_trans (hlo _) (h'.1 _).1) (h.2 e) (h'.2 e)

end ThermoCoreCompatibility.BeyondJunction

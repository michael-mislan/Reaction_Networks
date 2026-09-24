import proofs.ThermoCoreCompatibility.Hypergraph.GradedSource

namespace ThermoCoreCompatibility.Hypergraph.PairResponse

noncomputable def f (x : ℝ) : ℝ := (x+x^2)/2
noncomputable def g (x : ℝ) : ℝ := (x+2*x^2)/3

theorem interval_iff (x y : ℝ) : Ring.Productive x y ↔ g x < y ∧ y < f x := by
  unfold Ring.Productive f g
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem domain {x y : ℝ} (hx : 0 < x) (h : Ring.Productive x y) : x < 1 := by
  obtain ⟨h₁,h₂⟩ := h
  by_contra hn
  have hp := mul_nonneg (le_of_lt hx) (show 0 ≤ x-1 by linarith)
  nlinarith

theorem composition_identity (x : ℝ) :
    f (f x)-g x = x*(x-1)*(3*x^2+9*x+2)/24 := by
  unfold f g
  ring

theorem composition_lt {x : ℝ} (hx : 0 < x) (hu : x < 1) : f (f x) < g x := by
  have hq : 0 < 3*x^2+9*x+2 := by positivity
  have hn := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx (by linarith : x-1<0)) hq
  have he := composition_identity x
  linarith

theorem f_mono {x y : ℝ} (hx : 0 < x) (hxy : x < y) : f x < f y := by
  have hp := mul_pos (sub_pos.mpr hxy) (show 0 < y+x by linarith)
  unfold f
  nlinarith

theorem two_step {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : Ring.Productive x y) (hyz : Ring.Productive y z) : z < g x := by
  have h₁ := (interval_iff x y).mp hxy
  have h₂ := (interval_iff y z).mp hyz
  exact h₂.2.trans ((f_mono hy h₁.2).trans (composition_lt hx (domain hx hxy)))

theorem path_incompatible {L : ℕ} (hL : 2 ≤ L) (x : ℕ → ℝ)
    (hx : ∀ i ≤ L, 0 < x i)
    (he : ∀ i < L, Ring.Productive (x i) (x (i+1))) :
    ¬ Ring.Productive (x 0) (x L) := by
  have ht : x 2 < g (x 0) := two_step (hx 0 (by omega)) (hx 1 (by omega))
    (he 0 (by omega)) (he 1 (by omega))
  have hd : ∀ k, 2 ≤ k → k ≤ L → x k ≤ x 2 := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk hu
      by_cases hh : k=1
      · subst k; exact le_rfl
      · exact (Ring.productive_decreases (he k (by omega))).le.trans (ih (by omega) (by omega))
  intro hs
  have hb := (interval_iff (x 0) (x L)).mp hs
  exact (not_lt_of_ge (hd L hL le_rfl)) (ht.trans hb.1)

end ThermoCoreCompatibility.Hypergraph.PairResponse

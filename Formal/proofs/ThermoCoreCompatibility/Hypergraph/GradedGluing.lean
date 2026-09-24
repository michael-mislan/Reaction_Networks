import proofs.ThermoCoreCompatibility.Hypergraph.RingHyperedge

namespace ThermoCoreCompatibility.Hypergraph.Graded

noncomputable def state (height rank : ℕ) : ℝ := 1-(1/20)*(5/8)^(height-rank)

theorem state_bounds (height rank : ℕ) : 9/10 ≤ state height rank ∧ state height rank ≤ 1 := by
  have hp : 0 < (5/8 : ℝ)^(height-rank) := by positivity
  have hu := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 5/8)
    (by norm_num : (5/8 : ℝ) ≤ 1) (n := height-rank)
  unfold state
  constructor <;> linarith

theorem edge_productive {height r s : ℕ} (hs : s ≤ height) (hr : s = r+1) :
    Ring.Productive (state height r) (state height s) := by
  have he : height-r = (height-s)+1 := by omega
  have hp : 0 < (1/20 : ℝ)*(5/8)^(height-r) := by positivity
  have hu : (1/20 : ℝ)*(5/8)^(height-r) ≤ 1/20 := by
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 5/8)
      (by norm_num : (5/8 : ℝ) ≤ 1) (n := height-r)
    linarith
  have hstep : (1/20 : ℝ)*(5/8)^(height-s) = (8/5)*((1/20)*(5/8)^(height-r)) := by
    rw [he,pow_succ]
    ring
  unfold state
  rw [hstep]
  exact Ring.local_deletion hp hu

/-- Multiple shared interfaces glue on any finite graded directed incidence
pattern: every occurrence of a vertex is assigned exactly the same state. -/
theorem graded_common_state {V E : Type*} (src dst : E → V) (rank : V → ℕ)
    (height : ℕ) (hbound : ∀ v, rank v ≤ height)
    (hedge : ∀ e, rank (dst e) = rank (src e)+1) :
    ∃ x : V → ℝ, (∀ v, 9/10 ≤ x v ∧ x v ≤ 1) ∧
      ∀ e, Ring.Productive (x (src e)) (x (dst e)) := by
  exact ⟨fun v => state height (rank v),fun v => state_bounds height (rank v),
    fun e => edge_productive (hbound (dst e)) (hedge e)⟩

theorem edge_epsilon_bounds {x y : ℝ} (hx : 9/10 ≤ x) (_hxu : x ≤ 1)
    (h : Ring.Productive x y) :
    0 < 1-x ∧ (29/20)*(1-x) < 1-y ∧ 1-y < (5/3)*(1-x) := by
  obtain ⟨h₁,h₂⟩ := h
  have hp : 0 < 1-x := by nlinarith
  have hsq : (1-x)^2 ≤ (1-x)/10 := by
    have hh := mul_nonneg (le_of_lt hp) (show 0 ≤ (1/10 : ℝ)-(1-x) by linarith)
    nlinarith
  exact ⟨hp,by nlinarith,by nlinarith [sq_nonneg (1-x)]⟩

/-- Acyclicity alone fails: two successive productive edges cannot coexist
with their shortcut in the same fixed box. Grading removes this obstruction. -/
theorem shortcut_obstruction {x y z : ℝ} (hx : 9/10 ≤ x) (hxu : x ≤ 1)
    (hy : 9/10 ≤ y) (hyu : y ≤ 1)
    (hxy : Ring.Productive x y) (hyz : Ring.Productive y z)
    (hxz : Ring.Productive x z) : False := by
  obtain ⟨he,hf,_⟩ := edge_epsilon_bounds hx hxu hxy
  obtain ⟨_,hg,_⟩ := edge_epsilon_bounds hy hyu hyz
  obtain ⟨_,_,hgg⟩ := edge_epsilon_bounds hx hxu hxz
  linarith

end ThermoCoreCompatibility.Hypergraph.Graded

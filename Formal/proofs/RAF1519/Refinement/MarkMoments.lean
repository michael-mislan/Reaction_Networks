import proofs.RAF1519.Refinement.PhysicalMarks

namespace RAF1519.Refinement
noncomputable section
open Classical
open scoped BigOperators
set_option maxHeartbeats 40000

def localMarkedMoment (m : PhysicalMark) (q : ℕ) (d V : ℝ) (N : Fin 7 → ℕ) : ℝ :=
  match m with
  | .inventory => (N 2:ℝ)+N 3+N 4+2^(q+1)*(N 5:ℝ)
  | .freeX => N 2
  | .foodU => V
  | .foodW => V
  | .service => d*(101/100)*(N 2:ℝ)+d*(N 6:ℝ)

/-- All positive reward moments are computed from literal channel rates.
    q=0 is the drift and q=1 the square-jump intensity. -/
theorem local_mark_moment (m : PhysicalMark) (q : ℕ) (r d V : ℝ) (hV : V ≠ 0) (N : Fin 7 → ℕ) :
    (∑ a : LocalChannel, (localReaction r d a).rate V N*(localMarkReward m a:ℝ)^(q+1)) =
      localMarkedMoment m q d V N := by
  cases m <;>
    simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  all_goals
    simp_rw [local_forward_binding r d V hV,local_reverse_binding r d V hV,
      local_food_rate,local_wash_rate r d V hV]
  all_goals
    norm_num [localMarkReward,localMarkedMoment,forwardRate,reverseRate,concentration,
      Fin.sum_univ_succ,Fin.succ,pow_succ]
  all_goals try field_simp
  all_goals ring_nf
  all_goals rfl

theorem graph_mark_moment {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (N : MolecularState n) (i : Fin n) (m : PhysicalMark) (q : ℕ) :
    (∑ a, molecularRate r d k V N a*(physicalMarkReward i m a:ℝ)^(q+1)) =
      localMarkedMoment m q (d i) V (fun s => N (i,s)) := by
  rw [Fintype.sum_sum_type]
  have he : (∑ a : Fin n × Fin n × Fin 7, molecularRate r d k V N (.inr a)*
      (physicalMarkReward i m (.inr a):ℝ)^(q+1)) = 0 := by simp [physicalMarkReward]
  rw [he,add_zero,Fintype.sum_prod_type,Finset.sum_eq_single i]
  · simp only [physicalMarkReward]
    change (∑ a : LocalChannel, (atNode i (localReaction (r i) (d i) a)).rate V N*
      (localMarkReward m a:ℝ)^(q+1)) = _
    simp_rw [atNode_rate]
    exact local_mark_moment m q (r i) (d i) V hV _
  · intro j _ hji
    simp [physicalMarkReward,hji]
  · simp

theorem graph_normalized_mark_moment {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (hV : V ≠ 0) (N : MolecularState n) (i : Fin n) (m : PhysicalMark) (q : ℕ) :
    (∑ a, molecularRate r d k V N a*(markIncrement V i m N a)^(q+1)) =
      localMarkedMoment m q (d i) V (fun s => N (i,s))/V^(q+1) := by
  simp only [markIncrement,div_pow,← mul_div_assoc,← Finset.sum_div]
  rw [graph_mark_moment r d k V hV]

end
end RAF1519.Refinement

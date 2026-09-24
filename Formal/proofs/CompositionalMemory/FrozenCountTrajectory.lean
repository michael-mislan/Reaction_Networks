import proofs.CompositionalMemory.CountJumpNonexplosion
import proofs.RandomViability.ChronologicalReward

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 60000

abbrev FrozenCountChannel (k : ℕ) := Unit ⊕ ModularChannel k
instance frozenCountChannel_singletons (k : ℕ) : MeasurableSingletonClass (FrozenCountChannel k) :=
  markSingletonClass

def frozenCountNext {k : ℕ} (N : ℕ) (s : ModularCountState k) (b : FrozenCountChannel k) : ModularCountState k :=
  b.elim (fun _ => s) (fun r => if 0 < s.2 ∧ s.2 < 2*(k*N) then modularNext s r else s)

def frozenCountRate {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (N : ℕ)
    (s : ModularCountState k) (b : FrozenCountChannel k) : ℝ :=
  b.elim (fun _ => 1) (fun r => if 0 < s.2 ∧ s.2 < 2*(k*N) then modularRate γ w s r else 0)

theorem frozen_count_rate_nonneg {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (s : ModularCountState k) (b : FrozenCountChannel k) :
    0 ≤ frozenCountRate γ w N s b := by
  cases b with
  | inl u => exact zero_le_one
  | inr b =>
    dsimp only [frozenCountRate,Sum.elim_inr]
    split_ifs
    · exact modular_rate_nonnegative γ w hγ hw s b
    · exact le_rfl

theorem frozen_count_total {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ) (N : ℕ) (s : ModularCountState k) :
    (∑ b,frozenCountRate γ w N s b)=1+(if 0 < s.2 ∧ s.2 < 2*(k*N) then ∑ r,modularRate γ w s r else 0) := by
  by_cases h : 0 < s.2 ∧ s.2 < 2*(k*N) <;> simp [frozenCountRate,Fintype.sum_sum_type,h]

theorem frozen_count_total_positive {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (s : ModularCountState k) :
    0 < ∑ b,frozenCountRate γ w N s b := by
  rw [frozen_count_total]
  split_ifs
  · have hn := Finset.sum_nonneg (fun r (_ : r ∈ Finset.univ) => modular_rate_nonnegative γ w hγ hw s r)
    linarith
  · norm_num

def frozenCountTrajectory {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (s : ModularCountState k) :=
  jumpTrajectoryLaw s (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)

def frozenCountMass {k : ℕ} (s : ModularCountState k) : ℝ := globalMoleculeCount s+1

theorem frozen_count_mass_pos {k : ℕ} (s : ModularCountState k) : 0 < frozenCountMass s := by
  have h := global_count_nonneg s
  unfold frozenCountMass
  linarith

/-- Positive initial membrane counts remain valid under every frozen or chemical update. -/
theorem frozen_count_next_positive {k : ℕ} (N : ℕ) (s : ModularCountState k) (hs : 0 < s.2)
    (b : FrozenCountChannel k) : 0 < (frozenCountNext N s b).2 := by
  cases b with
  | inl u => exact hs
  | inr r =>
    dsimp only [frozenCountNext,Sum.elim_inr]
    split_ifs
    · exact modular_membrane_positive s hs r
    · exact hs

/-- The literal growth process frozen at division is nonexplosive on its unbounded state space. -/
theorem frozen_count_nonexplosive {k : ℕ} (hk : 1 ≤ k) (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j,0 ≤ w i j) (N : ℕ) (s : ModularCountState k) :
    ∀ᵐ z ∂frozenCountTrajectory γ w hγ hw N s,
      Tendsto (waitingSum (fun i => (z (i+1)).2.2)) atTop atTop := by
  apply jump_times_diverge s (frozenCountNext N) (frozenCountRate γ w N)
    (frozen_count_rate_nonneg γ w hγ hw N) (frozen_count_total_positive γ w hγ hw N)
    frozenCountMass frozen_count_mass_pos 33 (by norm_num)
  · intro x
    by_cases hx : 0 < x.2 ∧ x.2 < 2*(k*N)
    · have hh := global_count_growth hk γ w x hx.1
      unfold modularGenerator at hh
      have he : (∑ r,modularRate γ w x r*(frozenCountMass (modularNext x r)-frozenCountMass x)) ≤
          33*frozenCountMass x := by
        simp only [frozenCountMass,add_sub_add_right_eq_sub]
        linarith only [hh]
      simpa [frozenCountNext,frozenCountRate,Fintype.sum_sum_type,hx] using he
    · have hp := frozen_count_mass_pos x
      simp [frozenCountNext,frozenCountRate,hx]
      positivity
  · intro B
    obtain ⟨q,hq,hbound⟩ := count_jump_rates_locally_bounded γ w hγ hw B
    refine ⟨(q : ℝ)+1,by positivity,?_⟩
    intro x hx
    rw [frozen_count_total]
    split_ifs with ha
    · have hmass : positiveCountMass ⟨x,ha.1⟩ ≤ B := by
        change globalMoleculeCount x ≤ B
        change globalMoleculeCount x+1 ≤ B at hx
        linarith only [hx]
      have hh := hbound ⟨x,ha.1⟩ hmass
      linarith only [hh]
    · have hp : (0 : ℝ) ≤ q := q.coe_nonneg
      linarith

end
end CompositionalMemory

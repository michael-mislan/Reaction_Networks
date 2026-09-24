import proofs.FiniteCopyReactor.PhaseWeights

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def phaseJump (w : PhaseWeights) (j : Fin 18) : ℝ :=
  w.x*((products j 2:ℝ)-(reactants j 2:ℝ))+
  w.c1*((products j 3:ℝ)-(reactants j 3:ℝ))+
  w.c2*((products j 4:ℝ)-(reactants j 4:ℝ))+
  w.z*((products j 5:ℝ)-(reactants j 5:ℝ))

theorem coordinate_jump_bound (j : Fin 18) (i : Fin 6) :
    |(products j i:ℝ)-(reactants j i:ℝ)| ≤ 2 := by
  fin_cases j <;> fin_cases i <;> norm_num [products,reactants]

theorem phase_jump_bound (w : PhaseWeights) (hw : w.Nonneg) (hm : w.mass ≤ 1) (j : Fin 18) :
    |phaseJump w j| ≤ 2 := by
  rcases hw with ⟨hx,h1,h2,hz⟩
  have hh (a : ℝ) (ha : 0 ≤ a) (i : Fin 6) :
      |a*((products j i:ℝ)-(reactants j i:ℝ))| ≤ 2*a := by
    rw [abs_mul,abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_left (coordinate_jump_bound j i) ha]
  unfold phaseJump
  have h := (abs_add_le (w.x*((products j 2:ℝ)-(reactants j 2:ℝ))+
    w.c1*((products j 3:ℝ)-(reactants j 3:ℝ))+w.c2*((products j 4:ℝ)-(reactants j 4:ℝ)))
    (w.z*((products j 5:ℝ)-(reactants j 5:ℝ))))
  have h' := abs_add_le (w.x*((products j 2:ℝ)-(reactants j 2:ℝ))+
    w.c1*((products j 3:ℝ)-(reactants j 3:ℝ))) (w.c2*((products j 4:ℝ)-(reactants j 4:ℝ)))
  have h'' := abs_add_le (w.x*((products j 2:ℝ)-(reactants j 2:ℝ)))
    (w.c1*((products j 3:ℝ)-(reactants j 3:ℝ)))
  dsimp [PhaseWeights.mass] at hm
  linarith [hh w.x hx 2,hh w.c1 h1 3,hh w.c2 h2 4,hh w.z hz 5]

theorem phase_actual_jump (w : PhaseWeights) (N : Counts) (j : Fin 18)
    (h : ∀ i, reactants j i ≤ N i) :
    w.obs (countNext N j)-w.obs N=phaseJump w j := by
  have hh := next_linear_difference N j ![0,0,w.x,w.c1,w.c2,w.z] h
  simpa [PhaseWeights.obs,phaseJump,Fin.sum_univ_succ,add_assoc] using hh

theorem phase_generator_linear (w : PhaseWeights) (N : Counts) (V r d : ℝ) :
    competitionGenerator N V (1/500000000) (1/10) r d w.obs =
      w.x*coordinateGenerator N V r d 2+w.c1*coordinateGenerator N V r d 3+
      w.c2*coordinateGenerator N V r d 4+w.z*coordinateGenerator N V r d 5 := by
  unfold coordinateGenerator competitionGenerator
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [PhaseWeights.obs]
  ring

def phaseDriftLower (w : PhaseWeights) (N : Counts) : ℝ :=
  w.x*(-70*(N 2)+20*(N 3)+38*(N 5))+w.c1*(-70*(N 3)+20*(N 4))+
  w.c2*(-70*(N 4))+w.z*(-70*(N 5)+20*(N 4))

theorem phase_generator_lower (w : PhaseWeights) (hw : w.Nonneg)
    (N : Counts) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hc : resourceGood N V) :
    phaseDriftLower w N ≤ competitionGenerator N V (1/500000000) (1/10) r d w.obs := by
  obtain ⟨h0,h1,h2,h3⟩ := count_phase_comparison N V r d hV hr hr' hd hd' hc
  rw [phase_generator_linear]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h0 hw.1) (mul_le_mul_of_nonneg_left h1 hw.2.1))
    (mul_le_mul_of_nonneg_left h2 hw.2.2.1)) (mul_le_mul_of_nonneg_left h3 hw.2.2.2)

theorem phase_step_obs (q : ℝ) (w : PhaseWeights) (N : Counts) :
    (phaseWeightStep q w).obs N=w.obs N+phaseDriftLower w N/q := by
  dsimp [phaseWeightStep,PhaseWeights.obs,phaseDriftLower]
  ring

end
end FiniteCopyReactor

import proofs.FiniteReservoir.SourceBounds
import proofs.FiniteCopyReactor.StockVariance

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

def internalRate (N : Counts) (V r alpha beta : ℝ) : CompetitionChannel → ℝ
  | .inl j => countRate N V (1/500000000) (1/10) r j
  | .inr j => countRate N V (if j=0 then alpha else beta) 1 0 (drivenBase j)

theorem internalRate_forward (N : Counts) (V r alpha beta : ℝ) :
    internalRate N V r alpha beta (.inr 0)=alpha*(N 2) := by
  simp [internalRate,drivenBase,countRate]

theorem internalRate_reverse (N : Counts) (V r alpha beta : ℝ) :
    internalRate N V r alpha beta (.inr 1)=beta*(N 0)*(N 1)/V := by
  norm_num [internalRate,drivenBase,countRate]

theorem rate_binding (s : State) (V r d R : ℝ) (j : CompetitionChannel) :
    rate s V r d R j=internalRate s.1 V r (alpha s.2 d R) (beta s.2 d R) j := by
  cases j with
  | inl j => fin_cases j <;> norm_num [rate,internalRate,CommonPhysicalRealization.physicalRate,countRate]
  | inr j => fin_cases j <;>
      norm_num [rate,internalRate,CommonPhysicalRealization.physicalRate,countRate,drivenBase,alpha,beta]

theorem internal_support (N : Counts) (V r alpha beta : ℝ) (j : CompetitionChannel)
    (h : internalRate N V r alpha beta j ≠ 0) :
    ∀ i, reactants (competitionBase j) i ≤ N i := by
  cases j with
  | inl j => exact rate_support N V _ _ r j h
  | inr j => exact rate_support N V _ 1 0 (drivenBase j) h

theorem internal_nonneg (N : Counts) (V r alpha beta : ℝ)
    (hV : 0 < V) (hr : 0 ≤ r) (ha : 0 ≤ alpha) (hb : 0 ≤ beta)
    (j : CompetitionChannel) : 0 ≤ internalRate N V r alpha beta j := by
  cases j with
  | inl j => exact countRate_nonneg N V _ _ r hV (by norm_num) (by norm_num) hr j
  | inr j =>
    apply countRate_nonneg N V _ 1 0 hV _ (by norm_num) (by norm_num)
    split_ifs <;> assumption

def generator (N : Counts) (V r alpha beta : ℝ) (f : Counts → ℝ) : ℝ :=
  ∑ j, internalRate N V r alpha beta j*(f (competitionNext N j)-f N)

def bathGenerator (s : State) (V r d R : ℝ) (f : State → ℝ) : ℝ :=
  ∑ j, rate s V r d R j*(f (next s j)-f s)

theorem generator_binding (s : State) (V r d R : ℝ) (f : Counts → ℝ) :
    bathGenerator s V r d R (fun t => f t.1)=
      generator s.1 V r (alpha s.2 d R) (beta s.2 d R) f := by
  unfold bathGenerator generator
  apply Finset.sum_congr rfl
  intro j _
  rw [rate_binding]
  rfl

theorem rated_linear (N : Counts) (V r alpha beta : ℝ)
    (j : CompetitionChannel) (a : Fin 6 → ℝ) :
    internalRate N V r alpha beta j *
      ((∑ i,a i*(competitionNext N j i:ℝ))-(∑ i,a i*(N i:ℝ))) =
      internalRate N V r alpha beta j *
      (∑ i,a i*((products (competitionBase j) i:ℝ)-(reactants (competitionBase j) i:ℝ))) := by
  by_cases h : internalRate N V r alpha beta j=0
  · simp [h]
  · rw [competitionNext,next_linear_difference N _ a (internal_support N V r alpha beta j h)]

theorem material_A_generator (N : Counts) (V r alpha beta : ℝ) :
    generator N V r alpha beta uCount=V-uCount N := by
  simp only [generator,uCount,rated_linear,u_units_stoich]
  simp only [Fintype.sum_sum_type,internalRate,competitionBase]
  have h := uCount_actual_drift N V (1/500000000) (1/10) r
  simp only [uCount,rated_linear_jump,u_units_stoich] at h
  rw [h]
  simp [Fin.sum_univ_succ,drivenBase,uUnitJump]

theorem material_B_generator (N : Counts) (V r alpha beta : ℝ) :
    generator N V r alpha beta wCount=V-wCount N := by
  simp only [generator,wCount,rated_linear,w_units_stoich]
  simp only [Fintype.sum_sum_type,internalRate,competitionBase]
  have h := wCount_actual_drift N V (1/500000000) (1/10) r
  simp only [wCount,rated_linear_jump,w_units_stoich] at h
  rw [h]
  simp [Fin.sum_univ_succ,drivenBase,wUnitJump]

theorem growth_expansion (N : Counts) (V r alpha beta : ℝ) :
    generator N V r alpha beta weightedCount =
      countGrowth N V (1/500000000) (1/10) r-alpha*(N 2)+beta*(N 0)*(N 1)/V := by
  have hj (j : CompetitionChannel) : internalRate N V r alpha beta j *
      (weightedCount (competitionNext N j)-weightedCount N)=
      internalRate N V r alpha beta j*weightedJump (competitionBase j) := by
    simp only [weighted_count_sum,rated_linear,weighted_stoich]
  have ho : countGrowth N V (1/500000000) (1/10) r=
      ∑ j,countRate N V (1/500000000) (1/10) r j*weightedJump j := by
    simp only [countGrowth,rated_weighted_jump]
  simp only [generator,hj,Fintype.sum_sum_type]
  rw [show (∑ j : Fin 18, internalRate N V r alpha beta (.inl j)*weightedJump
    (competitionBase (.inl j)))=countGrowth N V (1/500000000) (1/10) r from ho.symm]
  simp [Fin.sum_univ_succ,internalRate_forward,internalRate_reverse,competitionBase,drivenBase,weightedJump]
  ring

theorem count_correction (N : Counts) (V r alpha beta : ℝ) (hV : V ≠ 0) :
    generator N V r alpha beta weightedCount =
      V*Y (field r alpha beta (FiniteCopyReactor.concentration N V))+r*(N 2)/(5*V) := by
  rw [growth_expansion,countGrowth_expansion,weighted_drift]
  dsimp [FiniteCopyReactor.concentration]
  field_simp [hV]
  ring

theorem count_guarded_growth (N : Counts) (V r alpha beta : ℝ) (hV : 0 < V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hbox : RateBox alpha beta)
    (hA : 9/10 ≤ A (FiniteCopyReactor.concentration N V))
    (hB : 9/10 ≤ B (FiniteCopyReactor.concentration N V))
    (hY : Y (FiniteCopyReactor.concentration N V) ≤ 3/50) :
    (2/3)*weightedCount N+V/1000000000 ≤ generator N V r alpha beta weightedCount := by
  have hc : Nonneg (FiniteCopyReactor.concentration N V) := fun i => div_nonneg (Nat.cast_nonneg _) hV.le
  have h := mul_le_mul_of_nonneg_left
    (guarded_growth r alpha beta _ hc hr hr' hbox hA hB hY) hV.le
  rw [FiniteCopyReactor.normalized_stock] at h
  have he : V*((2/3)*(weightedCount N/V)+1/1000000000)=
    (2/3)*weightedCount N+V/1000000000 := by field_simp
  rw [he] at h
  rw [count_correction N V r alpha beta (ne_of_gt hV)]
  have hr0 : 0 ≤ r := by linarith
  exact h.trans (le_add_of_nonneg_right (by positivity))

end
end FiniteReservoir

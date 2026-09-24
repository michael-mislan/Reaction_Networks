import proofs.FiniteReservoir.CountSource

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

def coordinateGenerator (N : Counts) (V r alpha beta : ℝ) (i : Fin 6) : ℝ :=
  generator N V r alpha beta (fun X => (X i:ℝ))

theorem coordinate_generator_stoich (N : Counts) (V r alpha beta : ℝ) (i : Fin 6) :
    coordinateGenerator N V r alpha beta i = ∑ j,internalRate N V r alpha beta j *
      ((products (competitionBase j) i:ℝ)-(reactants (competitionBase j) i:ℝ)) := by
  unfold coordinateGenerator generator
  apply Finset.sum_congr rfl
  intro j _
  simpa using rated_linear N V r alpha beta j
    (fun k => if k=i then 1 else 0)

theorem phase_generator_expansion (N : Counts) (V r alpha beta : ℝ) :
    coordinateGenerator N V r alpha beta 2 =
      (1/500000000+beta)*(N 0)*(N 1)/V-
      (1+1/5000000000+alpha)*(N 2)-20*(N 2)*(N 0)/V+20*(N 3)+
      2*r*(N 5)-2*r*(N 2*(N 2-1):ℕ)/V ∧
    coordinateGenerator N V r alpha beta 3 =
      20*(N 2)*(N 0)/V-21*(N 3)-20*(N 3)*(N 1)/V+20*(N 4) ∧
    coordinateGenerator N V r alpha beta 4 =
      20*(N 3)*(N 1)/V-41*(N 4)+2*(N 5) ∧
    coordinateGenerator N V r alpha beta 5 =
      20*(N 4)-(3+r)*(N 5)+r*(N 2*(N 2-1):ℕ)/V := by
  simp only [coordinate_generator_stoich,Fintype.sum_sum_type,internalRate,competitionBase]
  norm_num [Fin.sum_univ_succ,countRate,products,reactants,internalRate_forward,internalRate_reverse,drivenBase]
  simp only [show (![0,0,1,0,0,0] : Fin 6 → ℕ) 2=1 by decide,
    show (![1,0,1,0,0,0] : Fin 6 → ℕ) 2=1 by decide,
    show (![0,0,2,0,0,0] : Fin 6 → ℕ) 2=2 by decide,
    show (![0,0,0,1,0,0] : Fin 6 → ℕ) 3=1 by decide,
    show (![0,1,0,1,0,0] : Fin 6 → ℕ) 3=1 by decide,
    show (![0,0,0,0,1,0] : Fin 6 → ℕ) 4=1 by decide,
    show (![0,0,0,0,0,1] : Fin 6 → ℕ) 5=1 by decide]
  norm_num
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring



theorem count_phase_comparison (N : Counts) (V : ℕ) (r alpha beta : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hbox : RateBox alpha beta) (hc : resourceGood N V) :
    -70*(N 2:ℝ)+20*(N 3)+38*(N 5) ≤ coordinateGenerator N V r alpha beta 2 ∧
    -70*(N 3:ℝ)+20*(N 4) ≤ coordinateGenerator N V r alpha beta 3 ∧
    -70*(N 4:ℝ) ≤ coordinateGenerator N V r alpha beta 4 ∧
    -70*(N 5:ℝ)+20*(N 4) ≤ coordinateGenerator N V r alpha beta 5 := by
  obtain ⟨hx,ha,hb,hz⟩ := phase_generator_expansion N V r alpha beta
  rw [hx,ha,hb,hz]
  have hn (i : Fin 6) : (0:ℝ) ≤ N i := Nat.cast_nonneg _
  have hprod (i j : Fin 6) : (N i:ℝ)*(N j)/(V:ℝ) ≤ (11/10)*(N i) := by
    apply (div_le_iff₀ hV).mpr
    have hh := mul_le_mul_of_nonneg_left (resource_count_cap N V hc j) (hn i)
    nlinarith
  have hfac : (N 2*(N 2-1):ℕ)/(V:ℝ) ≤ (11/10)*(N 2) := by
    exact (div_le_div_of_nonneg_right (factorial_le_square (N 2)) hV.le).trans
      (by simpa only [sq] using hprod 2 2)
  have hrf := mul_le_mul hr' hfac
    (show 0 ≤ (N 2*(N 2-1):ℕ)/(V:ℝ) by positivity) (by norm_num : (0:ℝ) ≤ 21)
  have hrl := mul_le_mul_of_nonneg_right hr (hn 5)
  have hru := mul_le_mul_of_nonneg_right hr' (hn 5)
  have hdx := mul_le_mul_of_nonneg_right hbox.alpha_upper (hn 2)
  have him : 0 ≤ (1/500000000+beta)*(N 0:ℝ)*(N 1)/(V:ℝ) := by
    have := hbox.beta_nonneg
    positivity
  have hpos : 0 ≤ r*(N 2*(N 2-1):ℕ)/(V:ℝ) :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hV.le
  have hp20 : 0 ≤ 20*(N 2:ℝ)*(N 0)/(V:ℝ) := by positivity
  have hp31 : 0 ≤ 20*(N 3:ℝ)*(N 1)/(V:ℝ) := by positivity
  have h20 (i j : Fin 6) : 20*(N i:ℝ)*(N j)/(V:ℝ) ≤ 22*(N i) := by
    convert mul_le_mul_of_nonneg_left (hprod i j) (by norm_num : (0:ℝ) ≤ 20) using 1 <;> ring
  have h42 : 2*r*(N 2*(N 2-1):ℕ)/(V:ℝ) ≤ (231/5)*(N 2) := by
    convert mul_le_mul_of_nonneg_left hrf (by norm_num : (0:ℝ) ≤ 2) using 1 <;> ring
  constructor
  · nlinarith [h20 2 0,hn 2]
  constructor
  · nlinarith [h20 3 1,hn 3]
  constructor
  · nlinarith [hn 4,hn 5]
  · nlinarith [hn 5]

end
end FiniteReservoir

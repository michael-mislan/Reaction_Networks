import proofs.FiniteCopyReactor.PhaseGenerator

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem count_phase_comparison (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hc : resourceGood N V) :
    -70*(N 2:ℝ)+20*(N 3)+38*(N 5) ≤ coordinateGenerator N V r d 2 ∧
    -70*(N 3:ℝ)+20*(N 4) ≤ coordinateGenerator N V r d 3 ∧
    -70*(N 4:ℝ) ≤ coordinateGenerator N V r d 4 ∧
    -70*(N 5:ℝ)+20*(N 4) ≤ coordinateGenerator N V r d 5 := by
  obtain ⟨hx,ha,hb,hz⟩ := phase_generator_expansion N V r d
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
  have hdx := mul_le_mul_of_nonneg_right hd' (hn 2)
  have him : 0 ≤ (1/500000000+d/8000000000)*(N 0:ℝ)*(N 1)/(V:ℝ) := by positivity
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
end FiniteCopyReactor

import proofs.CompositionalMemory.WideFiniteGenerator

namespace CompositionalMemory
open FiniteCopy FiniteIntegerRows
set_option maxHeartbeats 50000

/-- The finite model's literal generator is exactly the six-channel formula
with zero reward on artificial exit. -/
theorem wide_generator_literal (γ : ℝ) (hγ : 0 ≤ γ) (data : Nat → Array Int)
    (col : Nat) (j : Fin 26) (hj : j.val≠25)
    (x : Fin (16*(25+j.val)+1)) (y : Fin (4*(25+j.val)+1)) :
    (wideFiniteModel γ hγ).generator (wideValue data col) (some ⟨j,x,y⟩) =
      wideLiteral γ (25+j.val) (data (25+j.val)) (data (25+j.val+1))
        (x.val*(4*(25+j.val)+1)+y.val) col 0 := by
  rcases wide_index_coordinates j x y with ⟨hix,hiy⟩
  simp only [wideLiteral,hix,hiy]
  by_cases hx : x.val=0
  · norm_num [FiniteJumpModel.generator,wideFiniteModel,wideRate,wideNext,hj,hx,
      Fin.sum_univ_succ]
    simp only [wideValue_clipped]
    simp only [wideValue,hx,zero_mul,zero_add]
  · have hpos : 0 < x.val := by omega
    have hjlt : j.val < 25 := by omega
    have hg := wideValue_growth data col j hjlt x y hpos
    norm_num [FiniteJumpModel.generator,wideFiniteModel,wideRate,wideNext,hj,hx,
      Fin.sum_univ_succ]
    rw [hg]
    simp only [wideValue_clipped]
    simp only [wideValue]
    push_cast [Nat.cast_sub (by omega : 1 ≤ x.val)]
    ring

end CompositionalMemory

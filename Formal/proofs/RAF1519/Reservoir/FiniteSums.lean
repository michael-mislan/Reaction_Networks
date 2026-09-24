import Mathlib

namespace RAF1519.Reservoir
open scoped BigOperators

theorem sum_six (v : Fin 6 → ℝ) :
    (∑ j, v j) = v 0+v 1+v 2+v 3+v 4+v 5 := by
  simp [Fin.sum_univ_succ]
  ring

theorem sum_nine (v : Fin 9 → ℝ) :
    (∑ j, v j) = v 0+v 1+v 2+v 3+v 4+v 5+v 6+v 7+v 8 := by
  simp [Fin.sum_univ_succ]
  ring

end RAF1519.Reservoir

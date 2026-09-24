import proofs.PersisterMemory.ControlSource

namespace PersisterMemory
open Source
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail
def improvedWeight : Fin 6 → ℚ := ![1419,1105,1000,8423,4305,10765]
theorem improved_pulse_certificate (i : Fin 6) :
    meanAction (3/10) improvedWeight i ≤ -(21/200)*improvedWeight i ∧
    1000 ≤ improvedWeight i ∧ improvedWeight i ≤ 10765 := by
  fin_cases i <;> norm_num [meanAction,molecular,daughter,death,improvedWeight]
end PersisterMemory

import proofs.FutileCycle.PrincipalAnnihilator

namespace FutileCycle

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem mask_coverage : ∀ s : Fin 6 → Bool, ∃ m : Fin 64,
    ∀ i : Fin 6, m.val.testBit i.val = s i := by
  decide

theorem full_mask (i : Fin 6) : (63 : ℕ).testBit i.val = true := by
  fin_cases i <;> decide

end FutileCycle

import proofs.ProductiveRecovery.Source

namespace ProductiveRecovery
noncomputable section
open scoped BigOperators

theorem field_stoichiometry (r d : ℝ) (c : State) (i : Fin 6) :
    field r d c i = (if i=0 ∨ i=1 then 1 else 0) - c i +
      ∑ j : Fin 6, flux r d c j *
        ((CommonPhysicalRealization.pairRight j (i.castLE (by decide)) : ℝ) -
          CommonPhysicalRealization.pairLeft j (i.castLE (by decide))) := by
  rw [Fin.sum_univ_six]
  fin_cases i
  · change 1-c 0-flux r d c 0-flux r d c 1+flux r d c 5 = (if (0:Fin 6)=0 ∨ (0:Fin 6)=1 then 1 else 0) - c 0 + (flux r d c 0 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 1 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 2 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 3 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 4 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 5 * (((1:ℕ):ℝ)-(0:ℕ)))
    norm_num [Fin.ext_iff]
    ring
  · change 1-c 1-flux r d c 0-flux r d c 2+flux r d c 5 = (if (1:Fin 6)=0 ∨ (1:Fin 6)=1 then 1 else 0) - c 1 + (flux r d c 0 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 1 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 2 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 3 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 4 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 5 * (((1:ℕ):ℝ)-(0:ℕ)))
    norm_num [Fin.ext_iff]
    ring
  · change -c 2+flux r d c 0-flux r d c 1+2*flux r d c 4-flux r d c 5 = (if (2:Fin 6)=0 ∨ (2:Fin 6)=1 then 1 else 0) - c 2 + (flux r d c 0 * (((1:ℕ):ℝ)-(0:ℕ)) + flux r d c 1 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 2 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 3 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 4 * (((2:ℕ):ℝ)-(0:ℕ)) + flux r d c 5 * (((0:ℕ):ℝ)-(1:ℕ)))
    norm_num [Fin.ext_iff]
    ring
  · change -c 3+flux r d c 1-flux r d c 2 = (if (3:Fin 6)=0 ∨ (3:Fin 6)=1 then 1 else 0) - c 3 + (flux r d c 0 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 1 * (((1:ℕ):ℝ)-(0:ℕ)) + flux r d c 2 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 3 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 4 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 5 * (((0:ℕ):ℝ)-(0:ℕ)))
    norm_num [Fin.ext_iff]
    ring
  · change -c 4+flux r d c 2-flux r d c 3 = (if (4:Fin 6)=0 ∨ (4:Fin 6)=1 then 1 else 0) - c 4 + (flux r d c 0 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 1 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 2 * (((1:ℕ):ℝ)-(0:ℕ)) + flux r d c 3 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 4 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 5 * (((0:ℕ):ℝ)-(0:ℕ)))
    norm_num [Fin.ext_iff]
    ring
  · change -c 5+flux r d c 3-flux r d c 4 = (if (5:Fin 6)=0 ∨ (5:Fin 6)=1 then 1 else 0) - c 5 + (flux r d c 0 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 1 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 2 * (((0:ℕ):ℝ)-(0:ℕ)) + flux r d c 3 * (((1:ℕ):ℝ)-(0:ℕ)) + flux r d c 4 * (((0:ℕ):ℝ)-(1:ℕ)) + flux r d c 5 * (((0:ℕ):ℝ)-(0:ℕ)))
    norm_num [Fin.ext_iff]
    ring

end
end ProductiveRecovery

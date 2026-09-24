import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory
open Classical FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- Uniformization's exact channel equation for nonnegative, potentially infinite payoffs. -/
theorem uniformize_ennreal_step (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x,M.total x ≤ q) (H : α → ℝ≥0∞) (x : α) :
    ENNReal.ofReal q*(∑ y,ENNReal.ofReal ((M.uniformize q hq hbound).prob x y)*H y) =
      ENNReal.ofReal (q-M.total x)*H x+∑ r,ENNReal.ofReal (M.rate x r)*H (M.next x r) := by
  have hd : 0 ≤ 1-M.total x/q := sub_nonneg.mpr ((div_le_one hq).mpr (hbound x))
  have he (y : α) : ENNReal.ofReal ((M.uniformize q hq hbound).prob x y)=
      (if x=y then ENNReal.ofReal (1-M.total x/q) else 0)+
        ∑ r,if M.next x r=y then ENNReal.ofReal (M.rate x r/q) else 0 := by
    change ENNReal.ofReal ((if x=y then 1-M.total x/q else 0)+
      ∑ r,if M.next x r=y then M.rate x r/q else 0)=_
    have h1 : 0 ≤ if x=y then 1-M.total x/q else 0 := by split_ifs <;> positivity
    have h2 (r : β) : 0 ≤ if M.next x r=y then M.rate x r/q else 0 := by
      split_ifs
      · exact div_nonneg (M.nonneg x r) hq.le
      · exact le_rfl
    rw [ENNReal.ofReal_add h1 (Finset.sum_nonneg (fun r _ => h2 r)),
      ENNReal.ofReal_sum_of_nonneg (fun r _ => h2 r)]
    congr 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp
  have hs : (∑ y,ENNReal.ofReal ((M.uniformize q hq hbound).prob x y)*H y)=
      ENNReal.ofReal (1-M.total x/q)*H x+
        ∑ r,ENNReal.ofReal (M.rate x r/q)*H (M.next x r) := by
    simp_rw [he,add_mul,Finset.sum_add_distrib,Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    simp
  have hdiag : ENNReal.ofReal q*ENNReal.ofReal (1-M.total x/q)=ENNReal.ofReal (q-M.total x) := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  have hr (r : β) : ENNReal.ofReal q*ENNReal.ofReal (M.rate x r/q)=ENNReal.ofReal (M.rate x r) := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  rw [hs,mul_add,← mul_assoc,hdiag,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [← mul_assoc,hr]

end
end CompositionalMemory

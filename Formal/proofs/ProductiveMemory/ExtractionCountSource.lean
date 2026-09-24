import proofs.ProductiveMemory.ExtractionSource
import proofs.FiniteCopy.CountSource

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

def channelEnabled (n : Counts) : ExtractionChannel → Prop :=
  Sum.elim (reactants n) (fun _ => 1 ≤ n 2)
def channelNext (n : Counts) : ExtractionChannel → Counts :=
  Sum.elim (nextCounts n) (fun _ => ![n 0,n 1,n 2-1,n 3])

theorem channel_next_cast (n : Counts) (c : ExtractionChannel) (h : channelEnabled n c)
    (i : Fin 4) : (channelNext n c i:ℝ) = (n i:ℝ)+channelJump c i := by
  cases c with
  | inl r => exact nextCounts_cast n r h i
  | inr r =>
    change 1 ≤ n 2 at h
    fin_cases i <;> simp [channelNext,channelJump,Matrix.cons_val_two,Matrix.cons_val_three,
      Nat.cast_sub h,sub_eq_add_neg]

theorem channel_disabled_zero (rho : ℝ) (N : ℕ) (n : Counts) (c : ExtractionChannel)
    (h : ¬channelEnabled n c) : channelDensity rho (1/(N:ℝ)) (concentration N n) c = 0 := by
  cases c with
  | inl r => exact disabled_density_zero (1/100000) N n r h
  | inr r =>
    change ¬1 ≤ n 2 at h
    have hh : n 2 = 0 := by omega
    simp [channelDensity,concentration,hh]

theorem channel_concentration_next (N : ℕ) (n : Counts) (c : ExtractionChannel)
    (h : channelEnabled n c) : concentration N (channelNext n c) =
      fun i => concentration N n i+channelJump c i/(N:ℝ) := by
  funext i
  dsimp [concentration]
  rw [channel_next_cast n c h]
  ring

end
end ProductiveMemory

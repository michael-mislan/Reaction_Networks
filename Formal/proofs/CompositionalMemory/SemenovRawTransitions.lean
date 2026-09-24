import proofs.CompositionalMemory.SemenovInventoryDrift

namespace CompositionalMemory.Semenov

def rawChannelNext (n : Fin 8 → ℕ) : Channel → Fin 8 → ℕ
  | Sum.inl r => rawChemicalNext n r
  | Sum.inr (Sum.inl j) => fun i => n i+if i=j then 1 else 0
  | Sum.inr (Sum.inr j) => fun i => n i-if i=j then 1 else 0

theorem reactor_next_raw {B K : ℕ} (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Channel) :
    reactorNext B K (some (n,c)) r=
      encodeReactor B K (rawChannelNext (fun j => (n j).val) r) (c.val+channelFeedIncrement r) := by
  rcases r with r | (j | j) <;> rfl

theorem raw_channel_next_upper (n : Fin 8 → ℕ) (r : Channel) (i : Fin 8) :
    rawChannelNext n r i ≤ n i+1 := by
  rcases r with r | (j | j)
  · exact raw_chemical_next_upper n r i
  · dsimp only [rawChannelNext]
    split_ifs <;> omega
  · dsimp only [rawChannelNext]
    omega

theorem raw_channel_next_cast (volume : ℝ) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Channel)
    (hr : 0 < reactorRate volume (some (n,c)) r) (i : Fin 8) :
    (rawChannelNext (fun j => (n j).val) r i : ℝ)=((n i).val : ℝ)+channelJump r i := by
  rcases r with r | (j | j)
  · obtain ⟨ha,hb⟩ := positive_chemical_rate_requirements volume n c r hr
    exact raw_chemical_next_cast (fun j => (n j).val) r ha hb i
  · by_cases hij : i=j <;> simp [rawChannelNext,channelJump,hij]
  · have hj : 0 < (n j).val := by
      by_contra h
      have hz : (n j).val=0 := by omega
      simp only [reactorRate,hz,Nat.cast_zero,mul_zero,lt_self_iff_false] at hr
    by_cases hij : i=j
    · subst i
      simp [rawChannelNext,channelJump,Nat.cast_sub (show 1 ≤ (n j).val by omega),sub_eq_add_neg]
    · simp only [rawChannelNext,channelJump,if_neg hij,Nat.sub_zero,add_zero]

theorem raw_channel_concentration (volume : ℝ) (hv : volume ≠ 0) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Channel)
    (hr : 0 < reactorRate volume (some (n,c)) r) :
    (fun j => (rawChannelNext (fun i => (n i).val) r j : ℝ)/volume)=
      (fun j => ((n j).val : ℝ)/volume)+(1/volume) • channelJump r := by
  funext j
  rw [raw_channel_next_cast volume n c r hr j]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  field_simp

end CompositionalMemory.Semenov

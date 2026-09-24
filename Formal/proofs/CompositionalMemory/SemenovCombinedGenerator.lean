import proofs.CompositionalMemory.SemenovRawTransitions

namespace CompositionalMemory.Semenov
open FiniteCopy

theorem tube_raw_next_fits (zc : Fin 8 → Fin 17 → ℚ) (radius : ℚ)
    (hr : 0 ≤ radius) (t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (volume : ℝ) (hv : 0 < volume) (B : ℕ) (n : Fin 8 → ℕ)
    (hx : vectorSquares (fun j => (n j : ℝ)/volume-coefficientValue (zc j) t) ≤ (radius : ℝ)^2)
    (hcap : ∀ j,volume*(coordinateUpper zc radius j : ℝ)+1 ≤ (B : ℝ)) (r : Channel) (j : Fin 8) :
    rawChannelNext n r j ≤ B := by
  have hn := (div_le_iff₀ hv).mp (tube_coordinate_upper zc radius hr t hl hu
    (fun i => (n i : ℝ)/volume) hx j)
  have hu' : (rawChannelNext n r j : ℝ) ≤ (n j : ℝ)+1 := by
    exact_mod_cast raw_channel_next_upper n r j
  have hh : (rawChannelNext n r j : ℝ) ≤ (B : ℝ) := by
    nlinarith only [hn,hu',hcap j]
  exact_mod_cast hh

/-- Compare with raw chemical jumps before absorption, and add only the
variance drift of the centered feed counter. -/
theorem combined_generator_bound (B K : ℕ) (hK : 0 < K) (volume : ℝ) (hv : 0 ≤ volume)
    (E : (Fin 8 → ℕ) → ℝ) (hE : ∀ n,0 ≤ E n) (m0 t dE a : ℝ)
    (n : Fin 8 → Fin (B+1)) (c : Fin K)
    (hcap : ∀ r j,rawChannelNext (fun i => (n i).val) r j ≤ B)
    (hm : m0+volume*(1/500)*(15231/100000)*t ≤ (K : ℝ)/2)
    (hchem : dE+(∑ r,reactorRate volume (some (n,c)) r*
      (E (rawChannelNext (fun j => (n j).val) r)-E (fun j => (n j).val))) ≤ a) :
    dE-8*(volume*(1/500)*(15231/100000))*(c.val-(m0+volume*(1/500)*(15231/100000)*t))/(K : ℝ)^2+
      (nominalReactor B K volume hv).generator
        (reactorCombinedEnergy E m0 (volume*(1/500)*(15231/100000)) t) (some (n,c)) ≤
      a+4*(volume*(1/500)*(15231/100000))/(K : ℝ)^2 := by
  let rate := volume*(1/500)*(15231/100000)
  have hnxt (r : Channel) := encoded_combined_energy_upper B K hK E m0 rate t
    (rawChannelNext (fun j => (n j).val) r) (c.val+channelFeedIncrement r)
    (hE _) (fun _ => hcap r) hm
  have hgen : (nominalReactor B K volume hv).generator (reactorCombinedEnergy E m0 rate t) (some (n,c)) ≤
      (∑ r,reactorRate volume (some (n,c)) r*(E (rawChannelNext (fun j => (n j).val) r)-E (fun j => (n j).val)))+
      (∑ r,reactorRate volume (some (n,c)) r*(centeredInventory K m0 rate t
        ((c.val : ℝ)+(channelFeedIncrement r : ℝ))-centeredInventory K m0 rate t c.val)) := by
    unfold FiniteJumpModel.generator
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro r _
    have hh := mul_le_mul_of_nonneg_left
      (sub_le_sub_right (hnxt r) (reactorCombinedEnergy E m0 rate t (some (n,c))))
      (reactorRate_nonneg volume hv (some (n,c)) r)
    simp only [nominalReactor,reactor_next_raw]
    simp only [reactorCombinedEnergy,Nat.cast_add] at hh ⊢
    nlinarith only [hh]
  have hc := raw_inventory_generator volume m0 t n c
  change -8*rate*(c.val-(m0+rate*t))/(K : ℝ)^2+_=4*rate/(K : ℝ)^2 at hc
  change dE-8*rate*(c.val-(m0+rate*t))/(K : ℝ)^2+_ ≤ a+4*rate/(K : ℝ)^2
  dsimp only [rate] at hgen hc ⊢
  simp only [neg_mul,neg_div] at hc
  linarith only [hgen,hchem,hc]

end CompositionalMemory.Semenov

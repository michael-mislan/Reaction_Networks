import proofs.RandomViability.SingleIncidenceRewardNoise
import proofs.RandomViability.MarkedMassBalance

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 60000

def modifiedExportReward {n : ℕ} (p : Molecule n) (a : ℝ) (V : NNReal) :
    PhysicalCountChannel n → ℝ
  | .inl (.inr q) => singleIncidenceWeight p a q/V
  | _ => 0

theorem singleIncidence_food_weight_zero {n : ℕ} (p q : Molecule n) (a : ℝ)
    (hp : 2 < molLength p) (hq : molLength q ≤ 2) : singleIncidenceWeight p a q = 0 := by
  have hne : q ≠ p := by intro h; subst q; omega
  simp [singleIncidenceWeight, foodMassWeight, hq, hne]

theorem modified_export_lower {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha2 : a ≤ 2) (hp : a+3 ≤ (molLength p : ℝ)) (V : NNReal) (hV : 0 < (V : ℝ))
    (ch : PhysicalCountChannel n) :
    (3/5 : ℝ)*exportReward V ch ≤ modifiedExportReward p a V ch := by
  rcases ch with (f|q)|(b|c)
  · simp [exportReward, modifiedExportReward]
  · simpa only [exportReward, modifiedExportReward, mul_div_assoc] using
      div_le_div_of_nonneg_right (singleIncidence_weight_lower p q a ha2 hp) hV.le
  · simp [exportReward, modifiedExportReward]
  · simp [exportReward, modifiedExportReward]

theorem enabled_modified_reward_budget {n : ℕ} (p : Molecule n) (a : ℝ)
    (hp : 2 < molLength p) (V : NNReal) (hV : 0 < (V : ℝ))
    (N : Molecule n → ℕ) (ch : PhysicalCountChannel n)
    (he : ∀ q, physicalChannelInput ch q ≤ N q) :
    (weightedCountMass (singleIncidenceWeight p a) (unboundedPhysicalNext N ch)-
      weightedCountMass (singleIncidenceWeight p a) N)/V + modifiedExportReward p a V ch ≤
      2*halfModifiedInputReward p a V N ch := by
  let w := singleIncidenceWeight p a
  have hi (D : ℝ) : D/(V : ℝ) ≤ 2*(max 0 D/(2*V)) := by
    calc
      _ ≤ max 0 D/(V : ℝ) := div_le_div_of_nonneg_right (le_max_right _ _) hV.le
      _ = _ := by field_simp
  rcases ch with (f|q)|(b|c)
  · simp only [modifiedExportReward, halfModifiedInputReward, mul_zero, add_zero]
    rw [unboundedPhysicalNext, if_pos he, weightedCountMass_change _ _ _ _ he]
    have hf := singleIncidence_food_weight_zero p f.val a hp (Finset.mem_filter.mp f.property).2
    simp [weightedCountMass, physicalChannelInput, physicalChannelOutput, singleCount, mul_ite, hf]
  · simp only [modifiedExportReward, halfModifiedInputReward, mul_zero]
    rw [unboundedPhysicalNext, if_pos he, weightedCountMass_change _ _ _ _ he]
    simp [weightedCountMass, physicalChannelInput, physicalChannelOutput, singleCount, mul_ite]
    ring_nf
    exact le_rfl
  · simpa only [modifiedExportReward, halfModifiedInputReward, add_zero] using hi
      (weightedCountMass w (unboundedPhysicalNext N (.inr (.inl b)))-weightedCountMass w N)
  · simpa only [modifiedExportReward, halfModifiedInputReward, add_zero] using hi
      (weightedCountMass w (unboundedPhysicalNext N (.inr (.inr c)))-weightedCountMass w N)

theorem marked_modified_prefix_balance {n : ℕ} (p : Molecule n) (a : ℝ)
    (hp : 2 < molLength p) (c : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ)) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hr : ∀ i,jumpPositiveRate (unboundedPhysicalRate c V 1 basal cat) (z i).1 (z (i+1)))
    (K : ℕ) :
    weightedCountMass (singleIncidenceWeight p a) (z K).1/V +
      markedWindowReward (fun _ => modifiedExportReward p a V) z 0 K ≤
    weightedCountMass (singleIncidenceWeight p a) (z 0).1/V +
      2*markedWindowReward (halfModifiedInputReward p a V) z 0 K := by
  induction K with
  | zero => simp [markedWindowReward]
  | succ K ih =>
    obtain ⟨ch,hch,hrate⟩ := hr K
    obtain ⟨b,hb,hn⟩ := hc K
    have heq : b = ch := Sum.inr.inj (hb.symm.trans hch)
    subst b
    have hen : ∀ q, physicalChannelInput ch q ≤ (z K).1 q := by
      by_contra h
      simp [unboundedPhysicalRate,h] at hrate
    have hstep := enabled_modified_reward_budget p a hp V hV (z K).1 ch hen
    rw [← hn] at hstep
    simp only [marked_window_reward_succ,Nat.zero_add,hch,Sum.elim_inr]
    rw [sub_div] at hstep
    linarith only [ih,hstep]

theorem marked_modified_export_lower {n : ℕ} (p : Molecule n) (a : ℝ)
    (ha2 : a ≤ 2) (hp : a+3 ≤ (molLength p : ℝ)) (V : NNReal) (hV : 0 < (V : ℝ))
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (J K : ℕ) :
    (3/5 : ℝ)*markedWindowReward (fun _ => exportReward V) z J K ≤
      markedWindowReward (fun _ => modifiedExportReward p a V) z J K := by
  unfold markedWindowReward
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  cases hm : (z (J+i+1)).2.1 with
  | inl u => simp
  | inr ch => exact modified_export_lower p a ha2 hp V hV ch

end
end RandomViability

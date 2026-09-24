import proofs.PowerLawSmallRAF.NucleusFailureSum

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section

def nucleusWeightedTail (r : ℝ) (m L : Nat) : ℝ :=
  ∑ k : Fin L, if m ≤ k.val then 2*(2*r)^k.val else 0

theorem nucleusWeightedTail_identity (r : ℝ) (m L : Nat) (hL : m ≤ L) :
    nucleusWeightedTail r m L*(1-2*r) = 2*((2*r)^m-(2*r)^L) := by
  induction L,hL using Nat.le_induction with
  | base =>
    have hz : nucleusWeightedTail r m m = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by have hk := k.isLt; omega)]
    rw [hz]
    ring
  | succ L hL ih =>
    unfold nucleusWeightedTail at *
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,if_pos hL]
    rw [add_mul,ih,pow_succ]
    ring

theorem nucleusWeightedTail_le (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2) (m L : Nat) :
    nucleusWeightedTail r m L ≤ 2*(2*r)^m/(1-2*r) := by
  have hp : 0 < 1-2*r := by linarith
  by_cases hL : m ≤ L
  · apply (le_div_iff₀ hp).mpr
    rw [nucleusWeightedTail_identity r m L hL]
    have hh : 0 ≤ (2*r)^L := pow_nonneg (by positivity) _
    linarith
  · have hz : nucleusWeightedTail r m L = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by have hk := k.isLt; omega)]
    rw [hz]
    positivity

def sourceAboveSeedWords (m L : Nat) : Finset LigationWord :=
  (Finset.univ.image (@sourceOwnerWord L)).filter (fun w => m < w.length)

theorem mem_sourceAboveSeedWords (m L : Nat) (w : LigationWord) :
    w ∈ sourceAboveSeedWords m L ↔ m < w.length ∧ w.length ≤ L := by
  classical
  constructor
  · intro hw
    obtain ⟨hw,hm⟩ := Finset.mem_filter.mp hw
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨hm,?_⟩
    rw [sourceOwnerWord_length]
    have hx := x.1.isLt
    unfold molLength
    omega
  · rintro ⟨hm,hL⟩
    let x := ligationWordMolecule L w (by omega) hL
    have he : sourceOwnerWord x = w := by
      apply ligationWordCode_injective_of_length
      · rw [sourceOwnerWord_length,ligationWordMolecule_length]
      · rw [sourceOwnerWord_code,ligationWordMolecule_code]
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,he⟩,hm⟩

theorem sourceAboveSeedWords_card_le (m L : Nat) :
    (sourceAboveSeedWords m L).card ≤ 2^(L+1) := by
  apply (Finset.card_filter_le _ _).trans
  apply Finset.card_image_le.trans
  have hh := source_molecule_card_budget L
  simp only [Finset.card_univ]
  omega

theorem sourceAboveSeedWords_failure_sum_le (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2)
    (m L : Nat) :
    (∑ w ∈ sourceAboveSeedWords m L, r^(w.length-1)) ≤ 2*(2*r)^m/(1-2*r) := by
  classical
  have hs : (∑ w ∈ sourceAboveSeedWords m L, r^(w.length-1)) = nucleusWeightedTail r m L := by
    unfold sourceAboveSeedWords
    rw [Finset.sum_filter,Finset.sum_image (fun x _ y _ h => sourceOwnerWord_injective h)]
    simp only [sourceOwnerWord_length,molLength,Nat.add_sub_cancel]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hm : m ≤ k.val
    · have hh : m < k.val+1 := by omega
      simp [hh,hm,Word,pow_succ,mul_pow]
      ring
    · have hh : ¬ m < k.val+1 := by omega
      simp [hh,hm]
  rw [hs]
  exact nucleusWeightedTail_le r hr hr2 m L

theorem fixedSeedTail_tendsto_zero (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 1/2) :
    Tendsto (fun m : Nat => 2*(2*r)^m/(1-2*r)) atTop (𝓝 0) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 2*r)
    (by linarith : 2*r<1)
  simpa only [mul_zero,zero_div] using (hh.const_mul 2).div_const (1-2*r)

end
end PowerLawSmallRAF

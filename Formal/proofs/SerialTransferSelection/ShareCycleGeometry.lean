import proofs.SerialTransferSelection.ShareTransfer
import proofs.SerialTransferSelection.CycleProbability

namespace SerialTransferSelection
open ResourceLimitedCompetition HeritableCompositions FiniteCopy

theorem batch_share_floor (s t : PopulationState) (b : Bool) (q : ℝ)
    (hshare : q ≤ ancestralShare b s) (hgrow : ancestralMembrane b s.live ≤ ancestralMembrane b t.live)
    (hcons : membrane t.live=4*membrane s.live) : q/4 ≤ ancestralShare b t := by
  apply (div_le_div_of_nonneg_right hshare (by norm_num : (0 : ℝ) ≤ 4)).trans
  unfold ancestralShare
  rw [hcons,Nat.cast_mul,Nat.cast_ofNat]
  have hg : (ancestralMembrane b s.live : ℝ) ≤ ancestralMembrane b t.live := by exact_mod_cast hgrow
  have hh := div_le_div_of_nonneg_right hg (by positivity : (0 : ℝ) ≤ 4*(membrane s.live : ℝ))
  convert hh using 1
  ring

theorem ready_share_count (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (zL zH : ℝ) (s : ReadyPopulation N M zL zH) (b : Bool) :
    ancestralShare b s.val/2 ≤ (ancestralCount b s.val.live : ℝ)/(M : ℝ) := by
  have hs := readyPopulation_ready N M zL zH s
  have hW := membrane_lower N s.val.live (fun c hc => (hs.2.2.2.1 c hc).1)
  rw [hs.1] at hW
  have hC := (ancestral_count_bounds N b s.val.live (fun c hc =>
    ⟨(hs.2.2.2.1 c hc).1,(hs.2.2.2.1 c hc).2.le⟩)).2
  exact count_share_conversion _ _ _ (N : ℝ) (M : ℝ) (Nat.cast_nonneg _) (by exact_mod_cast hN)
    (by exact_mod_cast hM) (by exact_mod_cast hW) (by exact_mod_cast hC)

theorem selected_return_share_recurrence (N M : ℕ) (hN : 0 < N) (hMpos : 0 < M)
    (zL zH : ℝ) (s : ReadyPopulation N M zL zH) (t : PopulationState)
    (hL : 0 < t.live.length) (hM : M ≤ t.live.length)
    (hcons : membrane t.live=4*membrane s.val.live)
    (hgrow : ∀ b, ancestralMembrane b s.val.live ≤ ancestralMembrane b t.live)
    (ε : ℝ) (he : 0 ≤ ε) (he1 : ε < 1) (S : TransferSubset t.live.length M)
    (hg : S ∈ ancestralTransferGoodSet N M t hM ε)
    (y : ReadyPopulation N M zL zH) (hy : selectedAncestryPreserved N M zL zH t S y)
    (b : Bool) : (1-ε)/(4*(1+ε))*ancestralShare b s.val ≤ ancestralShare b y.val := by
  have hs := readyPopulation_ready N M zL zH s
  have hyr := readyPopulation_ready N M zL zH y
  have hW := membrane_lower N s.val.live (fun c hc => (hs.2.2.2.1 c hc).1)
  have hY := membrane_lower N y.val.live (fun c hc => (hyr.2.2.2.1 c hc).1)
  rw [hs.1] at hW
  rw [hyr.1] at hY
  have hw : 0 < membrane s.val.live := lt_of_lt_of_le (Nat.mul_pos hN hMpos) hW
  have hyw : 0 < membrane y.val.live := lt_of_lt_of_le (Nat.mul_pos hN hMpos) hY
  have hi (b : Bool) := transfer_ancestral_interval N M hN b t hL hM ε he S (hg b)
  have hu : (membrane y.val.live : ℝ) ≤
      (1+ε)*((M : ℝ)/(t.live.length : ℝ))*(membrane t.live : ℝ) := by
    rw [← ancestral_membrane_total y.val.live,← ancestral_membrane_total t.live]
    push_cast
    rw [(hy true).2,(hy false).2]
    nlinarith only [(hi true).2,(hi false).2]
  apply share_transfer_recurrence (ancestralMembrane b s.val.live) (membrane s.val.live)
    (ancestralMembrane b t.live) (membrane t.live) (ancestralMembrane b y.val.live)
    (membrane y.val.live) ((M : ℝ)/(t.live.length : ℝ)) ε (Nat.cast_nonneg _)
    (by exact_mod_cast hw) (by exact_mod_cast hyw) (by positivity) he he1
    (by exact_mod_cast hcons) (by exact_mod_cast hgrow b) _ hu
  rw [(hy b).2]
  exact (hi b).1

end SerialTransferSelection

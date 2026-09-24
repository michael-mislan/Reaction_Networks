import proofs.StartupCount.SourceFloor
import proofs.RandomViability.PhysicalMassLocalization
import proofs.RandomViability.PhysicalWindowGeometry

namespace StartupMarked
open Classical RandomViability StartupCount RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 50000

theorem source_guard_prefix {n : ℕ} (hn : 2 ≤ n) (cfg : SourceMoleculeFibreConfig n)
    (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (r : Reaction n)
    (hb : ∀ r,(basal r : ℝ) ≤ 4*(1/500000000 : ℝ))
    (hc : ∀ r q,(cat r q : ℝ) ≤ 16) (hfood : ∀ q,molLength q ≤ 2 → cfg q = ∅)
    (hl : molLength (reactionLeft r) = 2) (hr : molLength (reactionRight r) = 2)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinitM : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hinitL : ((z 0).1 (reactionLeft r) : ℝ)/V = 1)
    (hinitR : ((z 0).1 (reactionRight r) : ℝ)/V = 1)
    (hconsistent : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hnoiseM : massNoiseBound cfg V basal cat 200 (1/4) z)
    (hnoiseL : coordinateNoiseBound cfg V basal cat (reactionLeft r) 200 (1/100000) z)
    (hnoiseR : coordinateNoiseBound cfg V basal cat (reactionRight r) 200 (1/100000) z)
    (L : ℕ) (hL : prefixElapsed L (Preorder.frestrictLe L z) ≤ 199) :
    ∀ i ≤ L,countGuard V r (z i).1 := by
  have hm := prefix_elapsed_monotone z hh
  have hmass (i : ℕ) (hi : i ≤ L) : (countMass (z i).1 : ℝ) ≤ 11*V := by
    have ht := (hm hi).trans hL
    have he := physical_mass_localization hn cfg V hV basal cat 200 z hinitM hconsistent hh hnoiseM i
      (by linarith only [ht])
    have hb' := (div_le_iff₀ hV).mp he
    nlinarith only [hb',hV]
  have hactive (i : ℕ) (hi : i ≤ L) : ¬censoredNonfoodStop V 200 (massExitStop V) i (Preorder.frestrictLe i z) :=
    mass_exit_active_before_first_exit V 200 z (show i < L+1 by omega)
      (fun j hj => hmass j (by omega)) ((hm hi).trans_lt (by linarith only [hL]))
  have ht (i : ℕ) (hi : i < L) : (z (i+1)).2.2 ≤ 200-prefixElapsed i (Preorder.frestrictLe i z) := by
    have he := (hm (show i+1 ≤ L by omega)).trans hL
    dsimp only at he
    rw [prefixElapsed_restrict_succ] at he
    linarith only [he]
  have hf (q : Molecule n) (hq : molLength q = 2) (hinit : ((z 0).1 q : ℝ)/V = 1)
      (hnoise : coordinateNoiseBound cfg V basal cat q 200 (1/100000) z) (i : ℕ) (hi : i ≤ L) :
      foodFloor*V ≤ ((z i).1 q : ℝ) := by
    have he := physical_food_floor_from_noise cfg V hV basal cat hb hc hfood q hq 200
      (1/100000) (by norm_num) z i hinit (fun j _ => hconsistent j)
      (fun j hj => hactive j (hj.trans hi)) (fun j hj => ht j (hj.trans_le hi))
      (fun j _ => hh j) hnoise
    have he' : foodFloor ≤ ((z i).1 q : ℝ)/V := by
      convert he using 1
      norm_num [foodFloor]
    exact (le_div_iff₀ hV).mp he'
  exact fun i hi => ⟨hmass i hi,hf _ hl hinitL hnoiseL i hi,hf _ hr hinitR hnoiseR i hi⟩

theorem stock_at_holding {n : ℕ} (V : NNReal) (hV : 0 < (V : ℝ)) (r : Reaction n)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) (L : ℕ) (t : ℝ)
    (ht : 1 ≤ t) (ht' : t ≤ 199)
    (hguard : ∀ j ≤ L,countGuard V r (z j).1)
    (hpre : ∀ j ≤ L,prefixElapsed j (Preorder.frestrictLe j z) ≤ t)
    (hpost : t < prefixElapsed (L+1) (Preorder.frestrictLe (L+1) z))
    (hgood : z ∉ lowDuring (countGuard V r) (fun N => N (reactionProduct r)) (stockThreshold V) 1 199) :
    (1/3000000000000000000 : ℝ) ≤ ((z L).1 (reactionProduct r) : ℝ)/V := by
  have hk : stockThreshold V ≤ (z L).1 (reactionProduct r) := by
    by_contra h
    apply hgood
    refine ⟨t,ht,ht',L,hguard,?_,?_,by dsimp only; omega⟩
    · intro j hj
      simpa only [prefixElapsed_eq_jumpElapsed] using hpre j hj
    · simpa only [prefixElapsed_eq_jumpElapsed] using hpost
  have hceil : (V : ℝ)/3000000000000000000 ≤ (stockThreshold V : ℝ) := Nat.le_ceil _
  have hcount : (stockThreshold V : ℝ) ≤ (z L).1 (reactionProduct r) := by exact_mod_cast hk
  apply (le_div_iff₀ hV).mpr
  have he := hceil.trans hcount
  linarith only [he]

end
end StartupMarked

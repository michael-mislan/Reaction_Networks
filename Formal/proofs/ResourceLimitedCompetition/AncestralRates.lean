import proofs.ResourceLimitedCompetition.AncestralMembrane

namespace ResourceLimitedCompetition
open HeritableCompositions FiniteCopy CoreCouplingCAC Set

noncomputable def ancestralZ (tag : Bool) (cs : List TaggedCell) : ℝ :=
  (cs.map (fun c => if c.high=tag then (c.compartment.1 2 : ℝ) else 0)).sum

theorem ancestralZ_nonneg (tag : Bool) (cs : List TaggedCell) : 0 ≤ ancestralZ tag cs := by
  apply sum_map_nonneg
  intro c
  split_ifs <;> positivity

theorem ancestral_rate_envelope (tag : Bool) (cs : List TaggedCell) (lo hi : ℝ)
    (h : ∀ c ∈ cs, c.high=tag → lo*(c.compartment.2 : ℝ) ≤ (c.compartment.1 2 : ℝ) ∧
      (c.compartment.1 2 : ℝ) ≤ hi*(c.compartment.2 : ℝ)) :
    lo*(ancestralMembrane tag cs : ℝ) ≤ ancestralZ tag cs ∧
      ancestralZ tag cs ≤ hi*(ancestralMembrane tag cs : ℝ) := by
  induction cs with
  | nil => simp [ancestralZ]
  | cons c cs ih =>
    have ht := ih (fun d hd he => h d (by simp [hd]) he)
    by_cases he : c.high=tag
    · have hc := h c (by simp) he
      simp only [ancestralMembrane_cons,he,if_true,Nat.cast_add,ancestralZ,
        List.map_cons,List.sum_cons]
      change lo*((c.compartment.2 : ℝ)+(ancestralMembrane tag cs : ℝ)) ≤
          (c.compartment.1 2 : ℝ)+ancestralZ tag cs ∧
        (c.compartment.1 2 : ℝ)+ancestralZ tag cs ≤
          hi*((c.compartment.2 : ℝ)+(ancestralMembrane tag cs : ℝ))
      constructor <;> nlinarith only [hc.1,hc.2,ht.1,ht.2]
    · simpa [ancestralZ,he] using ht

theorem safe_ancestral_rates (N : ℕ) (hN : 0 < N) (zL zH : ℝ)
    (hzL : zL ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000))
    (hzH : zH ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000))
    (s : PopulationState) (hv : ValidVolumes N s)
    (he : ∀ c ∈ s.live, cellEnergy zL zH c < outerEnergy) :
    ((297/100 : ℝ)*(ancestralMembrane true s.live : ℝ) ≤ ancestralZ true s.live ∧
      ancestralZ true s.live ≤ 3*(ancestralMembrane true s.live : ℝ)) ∧
    ((99/100 : ℝ)*(ancestralMembrane false s.live : ℝ) ≤ ancestralZ false s.live ∧
      ancestralZ false s.live ≤ (101/100)*(ancestralMembrane false s.live : ℝ)) := by
  constructor
  · apply ancestral_rate_envelope
    intro c hc htag
    have hm : 0 < (c.compartment.2 : ℝ) := by exact_mod_cast hN.trans_le (hv c hc).1
    have henergy : highEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zH) i) ≤ 1/32000000 := by
      simpa only [cellEnergy,htag,if_true,outerEnergy] using (he c hc).le
    have hg := (high_safe_geometry zH hzH _ henergy).1
    exact ⟨(le_div_iff₀ hm).mp hg.1,(div_le_iff₀ hm).mp hg.2⟩
  · apply ancestral_rate_envelope
    intro c hc htag
    have hm : 0 < (c.compartment.2 : ℝ) := by exact_mod_cast hN.trans_le (hv c hc).1
    have henergy : lowEnergy (fun i => concentration c.compartment.2 c.compartment.1 i-
        pointOfState (lift sourceRates zL) i) ≤ 1/32000000 := by
      simpa only [cellEnergy,htag,Bool.false_eq_true,if_false,outerEnergy] using (he c hc).le
    have hg := (low_safe_geometry zL hzL _ henergy).1
    exact ⟨(le_div_iff₀ hm).mp hg.1,(div_le_iff₀ hm).mp hg.2⟩

end ResourceLimitedCompetition

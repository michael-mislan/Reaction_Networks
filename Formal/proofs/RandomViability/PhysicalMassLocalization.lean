import proofs.RandomViability.PhysicalMassComparison

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 100000

def massNoiseBound {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T η : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∀ k s,0 ≤ s → s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) →
    |massCompensationWithinInterval c V basal cat T z k s| ≤ η

theorem mass_noise_from_components {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T ηN ηF : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hN : ∀ k s,0 ≤ s → s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) →
      |nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s| ≤ ηN)
    (hF : ∀ q : Molecule n,molLength q ≤ 2 → coordinateNoiseBound c V basal cat q T ηF z) :
    massNoiseBound c V basal cat T (ηN+10*ηF) z := by
  intro k s hs ht
  exact mass_interval_noise_bound hn c V basal cat T z k s ηN ηF
    (hN k s hs ht) (fun q hq => hF q hq k s hs ht)

/-- No count state at a represented jump time strictly before T can exit.
This does not assume nonexplosion or that every physical time is represented. -/
theorem physical_mass_localization {n : ℕ} (hn : 2 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (T : ℝ) (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n))
    (hinit : (countMass (z 0).1 : ℝ)/V ≤ 10)
    (hc : ∀ i,jumpConsistent unboundedPhysicalNext (z i).1 (z (i+1)))
    (hh : ∀ i,0 ≤ (z (i+1)).2.2)
    (hnoise : massNoiseBound c V basal cat T (1/4) z)
    (J : ℕ) (hJ : prefixElapsed J (Preorder.frestrictLe J z) < T) :
    (countMass (z J).1 : ℝ)/V ≤ 21/2 := by
  suffices h : ∀ K,prefixElapsed K (Preorder.frestrictLe K z) < T →
      (countMass (z K).1 : ℝ)/V ≤ 21/2 from h J hJ
  have hm : Monotone (fun k => prefixElapsed k (Preorder.frestrictLe k z)) := by
    apply monotone_nat_of_le_succ
    intro k
    rw [prefixElapsed_restrict_succ]
    exact le_add_of_nonneg_right (hh k)
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro hK
    have hgood : ∀ i < K,(countMass (z i).1 : ℝ) ≤ 11*V := by
      intro i hi
      have hv := ih i hi ((hm hi.le).trans_lt hK)
      have he := (div_le_iff₀ hV).mp hv
      nlinarith only [he,hV]
    have hs : ∀ i < K,¬censoredNonfoodStop V T (massExitStop V) i (Preorder.frestrictLe i z) := by
      intro i hi
      exact mass_exit_active_before_first_exit V T z hi hgood ((hm hi.le).trans_lt hK)
    have ht : ∀ i < K,(z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
      intro i hi
      have he := (hm (show i+1 ≤ K by omega)).trans_lt hK
      dsimp only at he
      rw [prefixElapsed_restrict_succ] at he
      linarith only [he]
    have hend : censoredMassPrefix c V basal cat T z K ≤ (1/4 : ℝ) := by
      have he := hnoise K 0 le_rfl (le_min (hh K) (sub_nonneg.mpr hK.le))
      simp only [massCompensationWithinInterval,mul_zero,sub_zero,ite_self] at he
      exact (abs_le.mp he).2
    have hb := physical_mass_prefix_ceiling hn c V hV basal cat T (1/4) (by norm_num)
      z K hinit (fun i _ => hc i) hs ht (fun i _ => hh i)
      (by
        intro i hi s hsi
        exact (abs_le.mp (hnoise i s hsi.1 (le_min hsi.2 (hsi.2.trans (ht i hi))))).1)
      hend
    norm_num at hb ⊢
    exact hb

end
end RandomViability

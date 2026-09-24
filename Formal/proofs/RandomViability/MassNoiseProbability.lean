import proofs.RandomViability.PhysicalMassLocalization

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 100000

def nonfoodNoiseBound {n : ℕ} (c : SourceMoleculeFibreConfig n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal) (T η : ℝ)
    (z : ℕ → JumpState (Molecule n → ℕ) (PhysicalCountChannel n)) : Prop :=
  ∀ k s,0 ≤ s → s ≤ min (z (k+1)).2.2 (T-prefixElapsed k (Preorder.frestrictLe k z)) →
    |nonfoodCompensationWithinInterval c V basal cat T (massExitStop V) z k s| ≤ η

theorem six_food_coordinates {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card ↥(binaryFood n 2) = 6 := by
  have hh := food_length_sum hn (fun _ => (1 : ℝ))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
  norm_num at hh
  have hc : (binaryFood n 2).card = 6 := by exact_mod_cast hh
  simpa only [Fintype.card_coe] using hc

variable {n : ℕ} [MeasurableSpace (PhysicalCountChannel n)]
  [MeasurableSingletonClass (PhysicalCountChannel n)]

theorem physical_nonfood_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (δ T η : ℝ) (hδ : 0 < δ) (hT : 0 ≤ T) (hmargin : δ+(n : ℝ)/V ≤ η) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬nonfoodNoiseBound c V basal cat T η z} ≤
      2*ENNReal.ofReal (Real.exp (-(δ^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δ))))) := by
  apply le_trans (measure_mono ?_)
    (physical_nonfood_two_sided_interval_tail hn c V hV basal cat N hbasal hcat δ T hδ hT)
  intro z hz
  simp only [nonfoodNoiseBound] at hz
  push Not at hz
  obtain ⟨k,s,h0,hs,hlarge⟩ := hz
  exact ⟨k,s,h0,hs,hmargin.trans hlarge.le⟩

/-- Upper-measure estimate for the exact mass-noise condition used in localization.
Only the six food coordinates are charged; no host-size union factor occurs. -/
theorem physical_mass_noise_failure (hn : 4 ≤ n)
    (c : SourceMoleculeFibreConfig n) (V : NNReal) (hV : 0 < (V : ℝ))
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ)
    (hbasal : ∀ r,(basal r : ℝ) ≤ 1) (hcat : ∀ r q,(cat r q : ℝ) ≤ 16)
    (δN δF T ηN ηF : ℝ) (hδN : 0 < δN) (hδF : 0 < δF) (hT : 0 ≤ T)
    (hmarginN : δN+(n : ℝ)/V ≤ ηN) (hmarginF : δF+2/V ≤ ηF) :
    physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
      {z | ¬massNoiseBound c V basal cat T (ηN+10*ηF) z} ≤
      2*ENNReal.ofReal (Real.exp (-(δN^2*(V : ℝ)/(4*(n : ℝ)*(96011*T+δN)))))+
      12*ENNReal.ofReal (Real.exp (-(δF^2*(V : ℝ)/(4*(96000*T+2*δF))))) := by
  let μ := physicalTrajectoryLaw (by omega : 2 ≤ n) c V 1 hV (by norm_num) basal cat N
  let EN := {z | ¬nonfoodNoiseBound c V basal cat T ηN z}
  let EF := fun q : ↥(binaryFood n 2) => {z | ¬coordinateNoiseBound c V basal cat q.val T ηF z}
  let BF := 2*ENNReal.ofReal (Real.exp (-(δF^2*(V : ℝ)/(4*(96000*T+2*δF)))))
  have hs : {z | ¬massNoiseBound c V basal cat T (ηN+10*ηF) z} ⊆ EN ∪ ⋃ q,EF q := by
    intro z hz
    by_contra h
    have hN : nonfoodNoiseBound c V basal cat T ηN z := by
      by_contra hN
      exact h (Or.inl hN)
    have hF : ∀ q : Molecule n,molLength q ≤ 2 → coordinateNoiseBound c V basal cat q T ηF z := by
      intro q hq
      by_contra hqbad
      apply h
      apply Or.inr
      apply Set.mem_iUnion.mpr
      exact ⟨⟨q,by simpa only [binaryFood,Finset.mem_filter,Finset.mem_univ,true_and] using hq⟩,hqbad⟩
    exact hz (mass_noise_from_components (by omega) c V basal cat T ηN ηF z hN hF)
  have hF : μ (⋃ q,EF q) ≤ 6*BF := by
    calc
      _ ≤ ∑ q,μ (EF q) := measure_iUnion_fintype_le μ EF
      _ ≤ ∑ _q : ↥(binaryFood n 2),BF := Finset.sum_le_sum (fun q _ =>
        physical_noise_bound_failure (by omega) c V hV basal cat N hbasal hcat q.val
          δF T ηF hδF hT hmarginF)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,six_food_coordinates (by omega : 2 ≤ n),nsmul_eq_mul]
        norm_num
  calc
    _ ≤ μ (EN ∪ ⋃ q,EF q) := measure_mono hs
    _ ≤ μ EN+μ (⋃ q,EF q) := measure_union_le _ _
    _ ≤ _+6*BF := add_le_add
      (physical_nonfood_noise_failure hn c V hV basal cat N hbasal hcat δN T ηN hδN hT hmarginN) hF
    _ = _ := by dsimp [BF]; ring

end
end RandomViability

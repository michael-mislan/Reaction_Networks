import proofs.PowerLawSmallRAF.SourceLengthEscape
import proofs.PowerLawSmallRAF.SourceCriticalSecondMoment
import proofs.PowerLawSmallRAF.SourceGatewayFactorization
import proofs.HordijkSteelThreshold.BoundedRAFProbability

namespace PowerLawSmallRAF
open Classical Filter Topology RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold
noncomputable section
set_option maxHeartbeats 800000

def sourceEscapeProbability (a : ℝ) (n K : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if ∃ x ∈ temporaryReactionClosure 2 (Finset.univ.biUnion config), K < molLength x
    then sourcePowerLawConfigWeight a n config else 0

/-- An exact-source upper bound: escape plus one of finitely many short
catalyst/food-enabled channel incidences. No source coordinate independence
is required for this union bound. -/
theorem sourceFullRAFProbability_le_escape_add_seed (a : ℝ) (ha : 1 < a)
    (n K : Nat) (hn : 4 ≤ n) :
    sourceFullRAFProbability a n ≤ sourceEscapeProbability a n K +
      (Fintype.card (Molecule K) : ℝ)*68*
        (windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ)) := by
  let J := ↥(binaryFood n K) × PolymerSeedReaction n 2
  let w := sourcePowerLawConfigWeight a n
  let E := fun config : SourceMoleculeFibreConfig n =>
    ∃ x ∈ temporaryReactionClosure 2 (Finset.univ.biUnion config), K < molLength x
  have hpoint (config : SourceMoleculeFibreConfig n) :
      (if ∃ S : Finset (Reaction n), S.card ≤ Fintype.card (Reaction n) ∧
        IsRevRAF (binaryPolymerCRS n 2) (sourceCatalysisOfConfig config) S
        then w config else 0) ≤
      (if E config then w config else 0) +
        ∑ j : J, if j.2.val ∈ config j.1.val then w config else 0 := by
    have hw : 0 ≤ w config := sourcePowerLawConfigWeight_nonneg a n ha config
    have hs : 0 ≤ ∑ j : J, if j.2.val ∈ config j.1.val then w config else 0 :=
      Finset.sum_nonneg (fun _ _ => by split_ifs <;> linarith only [hw])
    split_ifs with hraf he
    · linarith
    · obtain ⟨S,_,hraf⟩ := hraf
      have hSH : S ⊆ Finset.univ.biUnion config := by
        intro r hr
        obtain ⟨x,k,hx,hcat⟩ := hraf.2.2 r hr
        exact Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,hcat⟩
      obtain ⟨r,hr,hseed⟩ := exists_rev_seed_of_foodGenerated _ S hraf.1 hraf.2.1
      obtain ⟨x,k,hx,hcat⟩ := hraf.2.2 r hr
      have hxH := temporaryReactionClosure_mono hSH
        ((mem_temporaryReactionClosure S x).mpr ⟨k,hx⟩)
      have hxK : molLength x ≤ K := Nat.le_of_not_gt (fun hh => he ⟨x,hxH,hh⟩)
      let j : J := (⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxK⟩⟩,⟨r,hseed⟩)
      have hsingle := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : J => if j.2.val ∈ config j.1.val then w config else 0)
        (fun _ _ => by dsimp only; split_ifs <;> linarith only [hw]) (Finset.mem_univ j)
      have hcat' : r ∈ config x := hcat
      simpa only [j,if_pos hcat',zero_add] using hsingle
    · linarith
    · linarith
  have hsum := Finset.sum_le_sum (fun config (_ : config ∈ Finset.univ) => hpoint config)
  rw [Finset.sum_add_distrib] at hsum
  have hj : (∑ config : SourceMoleculeFibreConfig n,
      ∑ j : J, if j.2.val ∈ config j.1.val then w config else 0) ≤
      (Fintype.card (Molecule K) : ℝ)*68*
        (windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ)) := by
    rw [Finset.sum_comm]
    have hh : (∑ j : J, ∑ config : SourceMoleculeFibreConfig n,
        if j.2.val ∈ config j.1.val then w config else 0) ≤
        ∑ _j : J, windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ) :=
      Finset.sum_le_sum (fun j _ => source_single_incidence_mass_le_mean_div a ha hn j.1.val j.2.val)
    apply hh.trans
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : Fintype.card J ≤ Fintype.card (Molecule K)*68 := by
      dsimp [J]
      rw [Fintype.card_prod,Fintype.card_coe]
      exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (card_polymerSeedReaction_le_68 n)
    have hm : 0 ≤ windowZipfMean a (sourceReactionCount n)/(sourceReactionCount n : ℝ) :=
      div_nonneg (windowZipfMean_nonneg a _ ha) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hm
  have hE : (∑ config : SourceMoleculeFibreConfig n,
      if E config then w config else 0) = sourceEscapeProbability a n K := by
    unfold sourceEscapeProbability
    apply Finset.sum_congr rfl
    intro config _
    dsimp only [E,w]
    congr 1
  rw [hE] at hsum
  exact hsum.trans (add_le_add_right hj (sourceEscapeProbability a n K))

theorem sourceExactCriticalOneIncidence_tendsto_zero :
    Tendsto (fun n : Nat => windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/
      (sourceReactionCount n : ℝ)) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : Nat => (sourceMoleculeCount n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceMoleculeCount_tendsto_atTop
  have hh := sourceExactCriticalFirstMoment_scaled_tendsto.mul hx.inv_tendsto_atTop
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [sourceMoleculeCount_tendsto_atTop.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (sourceMoleculeCount n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp only [Pi.inv_apply]
  field_simp [hn0]

theorem sourceExactCriticalBoundedSeedError_tendsto_zero (K : Nat) :
    Tendsto (fun n : Nat => (Fintype.card (Molecule K) : ℝ)*68*
      (windowZipfMean (2-2/(n : ℝ)) (sourceReactionCount n)/(sourceReactionCount n : ℝ)))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using sourceExactCriticalOneIncidence_tendsto_zero.const_mul
    ((Fintype.card (Molecule K) : ℝ)*68)

end
end PowerLawSmallRAF

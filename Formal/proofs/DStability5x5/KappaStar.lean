import proofs.DStability5x5.Cone

/-!
# The minimal destabilizing ratio is attained (Proposition 6.3, first half)

For a Hurwitz matrix `A` that is not D-stable, the set of ratio bounds `κ ≥ 1` at which `A` fails to be
`κ`-stable has a least element `κs`, and some contact realizes it: it lies in `K_κs` and no contact lies in a
smaller cone.  Proof: in homogeneous box coordinates the set of triples `(κ, e, ω)` with `e ∈ [1, κ]ⁿ`,
`ω ∈ [0, W]` and `G(e, ω) = 0` is compact below any failing `κ₀`, so its projection to `κ` has a minimum;
`ω = 0` is excluded because `A` is nonsingular.
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

theorem homContact_ne_zero_at_zero_freq {A : Matrix (Fin n) (Fin n) ℝ} (hH : HurwitzStable A)
    {e : Fin n → ℝ} (he : ∀ i, 0 < e i) : homContact A (e, 0) ≠ 0 := by
  intro hG
  obtain ⟨v, hv⟩ := (homContact_eq_zero_iff A (e, 0)).mp hG
  simp only [Complex.ofReal_zero, zero_mul] at hv
  exact no_zero_eigen_of_hurwitz A hH e he v hv

/-- **κ* is attained**: the least failing ratio bound exists and is realized by a contact of minimal spread. -/
theorem exists_least_unstable_ratio {A : Matrix (Fin n) (Fin n) ℝ} (hH : HurwitzStable A)
    (hnot : ¬ DStable A) :
    ∃ κs : ℝ, 1 ≤ κs ∧ ¬ KStable κs A ∧ (∀ κ, 1 ≤ κ → κ < κs → KStable κ A) ∧
      ∃ d, InCone κs d ∧ contactDet A d = 0 := by
  have hne : ∃ κ₀ : ℝ, 1 ≤ κ₀ ∧ ¬ KStable κ₀ A := by
    by_contra h
    push Not at h
    exact hnot ((dStable_iff_forall_kStable A).mpr h)
  obtain ⟨κ₀, hκ₀, hfail⟩ := hne
  set R : ℝ := ∑ i, ∑ j, |A i j| with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  set W : ℝ := κ₀ * R + 1 with hW
  let Z : Set (ℝ × ((Fin n → ℝ) × ℝ)) :=
    {z | z.1 ∈ Set.Icc 1 κ₀ ∧ (∀ i, 1 ≤ z.2.1 i ∧ z.2.1 i ≤ z.1) ∧ z.2.2 ∈ Set.Icc 0 W ∧
      homContact A z.2 = 0}
  have hZsub : Z ⊆ Set.Icc 1 κ₀ ×ˢ ((Set.pi Set.univ (fun _ => Set.Icc 1 κ₀)) ×ˢ Set.Icc 0 W) := by
    rintro ⟨κ, e, ω⟩ ⟨hκ, he, hω, -⟩
    refine ⟨hκ, fun i _ => ⟨(he i).1, le_trans (he i).2 hκ.2⟩, hω⟩
  have hZc : IsCompact Z := by
    refine IsCompact.of_isClosed_subset
      (isCompact_Icc.prod ((isCompact_univ_pi (fun _ => isCompact_Icc)).prod isCompact_Icc)) ?_ hZsub
    have h1 : IsClosed {z : ℝ × ((Fin n → ℝ) × ℝ) | z.1 ∈ Set.Icc 1 κ₀} :=
      isClosed_Icc.preimage continuous_fst
    have h2 : IsClosed {z : ℝ × ((Fin n → ℝ) × ℝ) | ∀ i, 1 ≤ z.2.1 i ∧ z.2.1 i ≤ z.1} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => ?_
      have hc : Continuous (fun z : ℝ × ((Fin n → ℝ) × ℝ) => z.2.1 i) :=
        (continuous_apply i).comp (continuous_fst.comp continuous_snd)
      exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_fst)
    have h3 : IsClosed {z : ℝ × ((Fin n → ℝ) × ℝ) | z.2.2 ∈ Set.Icc 0 W} :=
      isClosed_Icc.preimage (continuous_snd.comp continuous_snd)
    have h4 : IsClosed {z : ℝ × ((Fin n → ℝ) × ℝ) | homContact A z.2 = 0} :=
      isClosed_eq ((homContact_contDiff A).continuous.comp continuous_snd) continuous_const
    have : Z = {z : ℝ × ((Fin n → ℝ) × ℝ) | z.1 ∈ Set.Icc 1 κ₀} ∩
        {z | ∀ i, 1 ≤ z.2.1 i ∧ z.2.1 i ≤ z.1} ∩ {z | z.2.2 ∈ Set.Icc 0 W} ∩
        {z | homContact A z.2 = 0} := by
      ext z
      simp only [Z, Set.mem_setOf_eq, Set.mem_inter_iff]
      tauto
    rw [this]
    exact ((h1.inter h2).inter h3).inter h4
  -- a triple of Z from any failing ratio bound κ ∈ [1, κ₀]
  have hmem : ∀ κ, 1 ≤ κ → κ ≤ κ₀ → ¬ KStable κ A → κ ∈ Prod.fst '' Z := by
    intro κ hκ1 hκ2 hk
    rw [kStable_iff_no_cone_contact hκ1] at hk
    push Not at hk
    obtain ⟨d, hd, hc⟩ := hk hH
    obtain ⟨x, hxbox, hxpos, hxG⟩ := exists_box_of_cone_contact A hd hc
    have hfreq := abs_freq_le_of_homContact A
      (fun i => ⟨le_trans zero_le_one (hxbox i).1, (hxbox i).2⟩) hxG
    have hxW : x.2 ≤ W := by
      have h1 : x.2 ≤ κ * R := le_trans (le_abs_self _) hfreq
      have h2 : κ * R ≤ κ₀ * R := mul_le_mul_of_nonneg_right hκ2 hR0
      linarith
    exact ⟨(κ, x), ⟨⟨hκ1, hκ2⟩, fun i => hxbox i, ⟨hxpos.le, hxW⟩, hxG⟩, rfl⟩
  set T : Set ℝ := Prod.fst '' Z with hT
  have hTc : IsCompact T := hZc.image continuous_fst
  have hTne : T.Nonempty := ⟨κ₀, hmem κ₀ hκ₀ le_rfl hfail⟩
  have hTbdd : BddBelow T := hTc.bddBelow
  set κs := sInf T with hκs
  have hκsT : κs ∈ T := hTc.sInf_mem hTne
  obtain ⟨⟨κ', e, ω⟩, ⟨hκ', he, hω, hG⟩, hfst⟩ := hκsT
  simp only at hκ' he hω hG hfst
  -- ω > 0 because A is nonsingular
  have hωpos : 0 < ω := by
    rcases eq_or_lt_of_le hω.1 with h0 | h0
    · exfalso
      rw [← h0] at hG
      exact homContact_ne_zero_at_zero_freq hH (fun i => lt_of_lt_of_le one_pos (he i).1) hG
    · exact h0
  have hbox : InBox κ' e := fun i => he i
  obtain ⟨d, hd, hc⟩ := cone_contact_of_box hκ'.1 A (x := (e, ω)) hbox hωpos hG
  refine ⟨κ', hκ'.1, ?_, ?_, d, hd, hc⟩
  · rw [kStable_iff_no_cone_contact hκ'.1]
    rintro ⟨-, hno⟩
    exact hno ⟨d, hd, hc⟩
  · intro κ hκ1 hκlt
    by_contra hk
    have hκT : κ ∈ T := hmem κ hκ1 (le_trans hκlt.le hκ'.2) hk
    have h1 : sInf T ≤ κ := csInf_le hTbdd hκT
    have h2 : κ' = sInf T := hfst
    linarith

end DStability5x5

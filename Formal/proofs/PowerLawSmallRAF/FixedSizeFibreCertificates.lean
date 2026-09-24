import proofs.PowerLawSmallRAF.FiniteCertificateUnion

namespace PowerLawSmallRAF

/-- Uniform `d`-subsets of an `R`-element catalogue. -/
abbrev FixedSizeFibre (R d : Nat) :=
  ↥((Finset.univ : Finset (Fin R)).powersetCard d)

def fixedSizeFibreContains {R d : Nat} (required : Finset (Fin R))
    (fibre : FixedSizeFibre R d) : Prop :=
  required ⊆ fibre.1

instance fixedSizeFibreContainsDecidable {R d : Nat}
    (required : Finset (Fin R)) :
    DecidablePred (fixedSizeFibreContains (d := d) required) := by
  intro fibre
  unfold fixedSizeFibreContains
  infer_instance

@[simp] theorem card_fixedSizeFibre (R d : Nat) :
    Fintype.card (FixedSizeFibre R d) = Nat.choose R d := by
  simp [FixedSizeFibre]

/-- Count of fixed-size fibres containing one prescribed required set. -/
theorem card_fixedSizeFibre_containing {R d q : Nat}
    (required : Finset (Fin R)) (hcard : required.card = q)
    (hqd : q ≤ d) :
    (Finset.univ.filter
      (fixedSizeFibreContains (d := d) required)).card =
      Nat.choose (R - q) (d - q) := by
  let source := Finset.univ.filter
    (fixedSizeFibreContains (d := d) required)
  let target := ((Finset.univ : Finset (Fin R)).powersetCard d).filter
    (required ⊆ ·)
  have hcardEq : source.card = target.card := by
    apply Finset.card_bij (fun fibre _ => fibre.1)
    · intro fibre hfibre
      simp only [target, Finset.mem_filter, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      exact ⟨(Finset.mem_powersetCard.mp fibre.property).2,
        (Finset.mem_filter.mp hfibre).2⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro s hs
      have hs' := Finset.mem_filter.mp hs
      exact ⟨⟨s, hs'.1⟩, by
        simp only [source, Finset.mem_filter, Finset.mem_univ, true_and,
          fixedSizeFibreContains]
        exact hs'.2, rfl⟩
  rw [hcardEq]
  dsimp [target]
  rw [Finset.card_filter_powersetCard_subset]
  · simp [hcard]
  · exact Finset.subset_univ required
  · simpa [hcard] using hqd

/-- The normalized compatibility fraction is exactly the hypergeometric
containment probability used by the analytic envelope. -/
theorem fixedSizeFibre_containing_fraction {R d q : Nat}
    (required : Finset (Fin R)) (hcard : required.card = q)
    (hqd : q ≤ d) :
    ((Finset.univ.filter
      (fixedSizeFibreContains (d := d) required)).card : ℝ) /
        Fintype.card (FixedSizeFibre R d) =
      hypergeometricContain R q d := by
  rw [card_fixedSizeFibre_containing required hcard hqd,
    card_fixedSizeFibre]
  rfl

/-- One certificate layer with `q` prescribed nongateway channels has exactly
the hypergeometric fibre cost appearing in the PL43 envelope. -/
theorem fixedSizeCertificateUnion_uniformMass_le
    {Target Code : Type*} [Fintype Target] [Fintype Code]
    [DecidableEq Target] {R d q : Nat}
    (output : Code → Target) (required : Code → Finset (Fin R))
    (hcard : ∀ c, (required c).card = q)
    (hqd : q ≤ d) (hdR : d ≤ R)
    (hTarget : 0 < Fintype.card Target) :
    ((certificateUnion output
      (fun (c : Code) (fibre : FixedSizeFibre R d) =>
        fixedSizeFibreContains (required c) fibre)).card : ℝ) /
        (Fintype.card Target * Fintype.card (FixedSizeFibre R d)) ≤
      (Fintype.card Code : ℝ) / Fintype.card Target *
        hypergeometricContain R q d := by
  apply certificateUnion_uniformMass_le_codeRatio_mul
  · exact hTarget
  · simpa [card_fixedSizeFibre] using Nat.choose_pos hdR
  · intro c
    exact (fixedSizeFibre_containing_fraction (required c) (hcard c) hqd).le

end PowerLawSmallRAF

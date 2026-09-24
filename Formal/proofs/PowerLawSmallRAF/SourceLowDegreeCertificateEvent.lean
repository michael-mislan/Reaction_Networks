import proofs.PowerLawSmallRAF.LigationCertificateLayer

namespace PowerLawSmallRAF

open Filter Topology

/-- Exact joint uniform mass of all legal ligation certificates for the source
model at one size and one fixed catalyst degree. -/
noncomputable def sourceLowDegreeCertificateMass
    (n degree : Nat)
    (output : ∀ s, LegalLigationProgramCode 6 s → Fin (sourceMoleculeCount n))
    (required : ∀ s, LegalLigationProgramCode 6 s →
      Finset (Fin (sourceReactionCount n - 1))) : ℝ :=
  ((legalLigationCertificateEvent 6 (sourceMoleculeCount n)
      (sourceReactionCount n) degree (min n degree) output required).card : ℝ) /
    (sourceMoleculeCount n *
      Fintype.card (FixedSizeFibre (sourceReactionCount n - 1) (degree - 1)))

/-- Any correctly encoded family of source ligation certificates with one
gateway and `s-1` distinct nongateway channels has vanishing mass throughout
the low-degree regime `degree ≤ R_n/n^3`. -/
theorem sourceLowDegreeCertificateMass_tendsto_zero
    (degree : Nat → Nat)
    (output : ∀ n s,
      LegalLigationProgramCode 6 s → Fin (sourceMoleculeCount n))
    (required : ∀ n s,
      LegalLigationProgramCode 6 s →
        Finset (Fin (sourceReactionCount n - 1)))
    (hrequired : ∀ n, 7 ≤ n → ∀ s,
      s ∈ Finset.Icc 1 (min n (degree n)) →
      ∀ code, (required n s code).card = s - 1)
    (hdegree1 : ∀ᶠ n : Nat in atTop, 1 ≤ degree n)
    (hdegree : ∀ᶠ n : Nat in atTop,
      degree n ≤ sourceReactionCount n / n ^ 3) :
    Tendsto (fun n : Nat =>
      sourceLowDegreeCertificateMass n (degree n) (output n) (required n))
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : ℝ)) atTop (𝓝 0))
    (sourceLowDegreeGrammarEnvelope_tendsto_zero degree hdegree1 hdegree)
  · filter_upwards with n
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards [eventually_ge_atTop 7, hdegree1, hdegree] with n hn hd1 hd
    have htarget : 0 < sourceMoleculeCount n :=
      (pow_pos (by norm_num) n).trans_le (sourceMoleculeCount_bounds (by omega)).1
    have hdR : degree n ≤ sourceReactionCount n :=
      hd.trans (Nat.div_le_self _ _)
    exact legalLigationCertificateEvent_uniformMass_le_envelope
      6 (sourceMoleculeCount n) (sourceReactionCount n) (degree n)
      (min n (degree n)) (output n) (required n) (hrequired n hn)
      htarget hd1 hdR (Nat.min_le_right n (degree n))

end PowerLawSmallRAF

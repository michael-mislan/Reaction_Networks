import proofs.PowerLawSmallRAF.SourceOwnerCoverScaffold

namespace PowerLawSmallRAF

noncomputable section

open RAF.Polymer

/-- Irredundancy can be globalized: choosing one private reaction for every
owner automatically produces an injective gateway map. -/
theorem sourceIrredundantOwnerCover_exists_injective_privateGateway
    {n : Nat} {config : SourceMoleculeFibreConfig n}
    {S : Finset (Reaction n)} {H : Finset (Molecule n)}
    (h : SourceIrredundantOwnerCover config S H) :
    ∃ gateway : ↑H → Reaction n, Function.Injective gateway ∧
      ∀ x : ↑H, gateway x ∈ S ∧ gateway x ∈ config x.1 ∧
        ∀ y : ↑H, y ≠ x → gateway x ∉ config y.1 := by
  classical
  let gateway : ↑H → Reaction n := fun x =>
    Classical.choose (h.2 x.1 x.2)
  have hspec : ∀ x : ↑H,
      gateway x ∈ S ∧ gateway x ∈ config x.1 ∧
        ∀ y : ↑H, y ≠ x → gateway x ∉ config y.1 := by
    intro x
    have hs := Classical.choose_spec (h.2 x.1 x.2)
    refine ⟨hs.1, hs.2.1, ?_⟩
    intro y hyx
    apply hs.2.2 y.1 y.2
    intro heq
    apply hyx
    exact Subtype.ext heq
  refine ⟨gateway, ?_, hspec⟩
  intro x y hxy
  by_contra hxyne
  have hnot := (hspec x).2.2 y (fun hyx => hxyne hyx.symm)
  apply hnot
  rw [hxy]
  exact (hspec y).2.1

/-- Uniform `d`-fibres which contain one labelled owner's gateway while
avoiding every other labelled private gateway. -/
def privateGatewayFibreEvent {R d : Nat} (gateway : Fin R)
    (other : Finset (Fin R)) : Finset (FixedSizeFibre R d) :=
  Finset.univ.filter fun fibre =>
    gateway ∈ fibre.1 ∧ Disjoint fibre.1 other

/-- Exact private-gateway count.  Once the owner's own gateway is fixed, its
remaining `d-1` channels must be selected from the complement of all `k`
labelled private gateways. -/
theorem card_privateGatewayFibreEvent {R d k : Nat} (gateway : Fin R)
    (other : Finset (Fin R)) (hg : gateway ∉ other)
    (hcard : other.card = k - 1) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (privateGatewayFibreEvent (d := d) gateway other).card =
      Nat.choose (R - k) (d - 1) := by
  classical
  let allowed := otherᶜ
  have hgAllowed : gateway ∈ allowed := by simp [allowed, hg]
  let target := (allowed.powersetCard d).filter ({gateway} ⊆ ·)
  have hcardEq : (privateGatewayFibreEvent (d := d) gateway other).card =
      target.card := by
    apply Finset.card_bij (fun fibre _ => fibre.1)
    · intro fibre hfibre
      have hp := (Finset.mem_filter.mp hfibre).2
      dsimp only [target]
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_compl_iff_disjoint_right.mpr hp.2,
          (Finset.mem_powersetCard.mp fibre.property).2⟩
      · simpa using hp.1
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro A hA
      have hparts : A ∈ allowed.powersetCard d ∧ {gateway} ⊆ A := by
        simpa only [target, Finset.mem_filter] using hA
      have hpower := Finset.mem_powersetCard.mp hparts.1
      refine ⟨⟨A, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ A, hpower.2⟩⟩, ?_, rfl⟩
      simp only [privateGatewayFibreEvent, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨(Finset.singleton_subset_iff.mp hparts.2),
        Finset.subset_compl_iff_disjoint_right.mp hpower.1⟩
  rw [hcardEq]
  have hcount := Finset.card_filter_powersetCard_subset
    ({gateway} : Finset (Fin R)) allowed d (by simpa using hgAllowed)
    (by simpa using hd)
  change target.card = _
  dsimp only [target]
  rw [hcount]
  have hallowed : allowed.card = R - (k - 1) := by
    dsimp only [allowed]
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hkR : k ≤ R := by
    have hproper : other ≠ (Finset.univ : Finset (Fin R)) := by
      intro heq
      have : gateway ∈ other := by rw [heq]; simp
      exact hg this
    have hlt := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ other, hproper⟩)
    rw [Finset.card_univ, Fintype.card_fin, hcard] at hlt
    omega
  rw [hallowed]
  simp only [Finset.card_singleton]
  congr 1
  rw [Nat.sub_sub, Nat.sub_add_cancel hk]

/-- All other labelled private gateways as seen from owner `i`. -/
def otherPrivateGateways {R k : Nat} (gateway : Fin k → Fin R)
    (i : Fin k) : Finset (Fin R) :=
  ((Finset.univ : Finset (Fin k)).erase i).image gateway

theorem card_otherPrivateGateways {R k : Nat} (gateway : Fin k → Fin R)
    (hgateway : Function.Injective gateway) (i : Fin k) :
    (otherPrivateGateways gateway i).card = k - 1 := by
  rw [otherPrivateGateways, Finset.card_image_of_injective _ hgateway,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

theorem own_not_mem_otherPrivateGateways {R k : Nat}
    (gateway : Fin k → Fin R) (hgateway : Function.Injective gateway)
    (i : Fin k) : gateway i ∉ otherPrivateGateways gateway i := by
  intro hi
  rw [otherPrivateGateways, Finset.mem_image] at hi
  obtain ⟨j, hj, hji⟩ := hi
  have : j = i := hgateway hji
  subst j
  exact (Finset.mem_erase.mp hj).1 rfl

noncomputable def privateGatewayDegreeProbability
    (R k d : Nat) : ℝ :=
  if d = 0 then 0 else
    (Nat.choose (R - k) (d - 1) : ℝ) / Nat.choose R d

/-- Product event in which every labelled owner has its own private gateway. -/
def privateGatewayConfigEvent {R k : Nat} (gateway : Fin k → Fin R)
    (degree : Fin k → Nat) :
    Finset (VariableFixedSizeFibreConfig R degree) :=
  Fintype.piFinset fun i =>
    privateGatewayFibreEvent (d := degree i) (gateway i)
      (otherPrivateGateways gateway i)

/-- Exact conditional product probability for a fixed injective private
gateway labelling and a fixed degree vector. -/
theorem privateGatewayConfigEvent_fraction {R k : Nat}
    (gateway : Fin k → Fin R) (hgateway : Function.Injective gateway)
    (degree : Fin k → Nat) (hk : 1 ≤ k) (hdegree : ∀ i, 1 ≤ degree i) :
    ((privateGatewayConfigEvent gateway degree).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) =
      ∏ i, privateGatewayDegreeProbability R k (degree i) := by
  have hfactor : ∀ i : Fin k,
      (privateGatewayFibreEvent (d := degree i) (gateway i)
        (otherPrivateGateways gateway i)).card =
        Nat.choose (R - k) (degree i - 1) := by
    intro i
    exact card_privateGatewayFibreEvent (gateway i)
      (otherPrivateGateways gateway i)
      (own_not_mem_otherPrivateGateways gateway hgateway i)
      (card_otherPrivateGateways gateway hgateway i) hk (hdegree i)
  rw [privateGatewayConfigEvent, Fintype.card_piFinset, Fintype.card_pi]
  simp_rw [hfactor]
  simp_rw [card_fixedSizeFibre]
  push_cast
  simp only [privateGatewayDegreeProbability, if_neg (Nat.ne_of_gt (hdegree _)),
    Finset.prod_div_distrib]

/-- Exact one-owner mixed private-gateway cost under the capped source degree
law. -/
noncomputable def sourcePrivateGatewayMass (a : ℝ) (R k : Nat) : ℝ :=
  ∑ d ∈ Finset.range R,
    cappedZipfDegreeMass a R d * privateGatewayDegreeProbability R k d

/-- The private-gateway factor splits into incidence of the owner's own
gateway and conditional avoidance of the other `k-1` gateways. -/
theorem privateGatewayDegreeProbability_eq_hit_mul_miss
    {R k d : Nat} (hk : 1 ≤ k) (hkR : k ≤ R)
    (hd : 1 ≤ d) (hdR : d ≤ R) :
    privateGatewayDegreeProbability R k d =
      hypergeometricContain R 1 d *
        hypergeometricGatewayMiss (R - 1) (k - 1) (d - 1) := by
  rw [privateGatewayDegreeProbability, if_neg (Nat.ne_of_gt hd)]
  rw [hypergeometricContain_eq_symmetricChoose R 1 d hd hdR]
  simp only [Nat.choose_one_right, hypergeometricGatewayMiss]
  have hsub : (R - 1) - (k - 1) = R - k := by omega
  rw [hsub]
  have hchooseR : (Nat.choose R d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hdR).ne'
  have hchooseSub : (Nat.choose (R - 1) (d - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : d - 1 ≤ R - 1)).ne'
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
  have hcross := Nat.choose_mul (n := R) (k := d) (s := 1) hd
  have hcross' : (Nat.choose R d : ℝ) * (d : ℝ) =
      (R : ℝ) * Nat.choose (R - 1) (d - 1) := by
    rw [show Nat.choose d 1 = d by simp,
      show Nat.choose R 1 = R by simp,
      show R - 1 = R - 1 by rfl,
      show d - 1 = d - 1 by rfl] at hcross
    exact_mod_cast hcross
  field_simp [hchooseR, hchooseSub, hR0]
  nlinarith

theorem powerLawMoleculeGatewayHit_one_eq_mean_div
    (a : ℝ) (R : Nat) (ha : 1 < a) (hR : 2 ≤ R) :
    powerLawMoleculeGatewayHit a R 1 = windowZipfMean a R / R := by
  rw [powerLawMoleculeGatewayHit_eq_sum a R 1 ha hR]
  have hpoint : ∀ d ∈ Finset.range R,
      1 - hypergeometricGatewayMiss R 1 d = (d : ℝ) / R := by
    intro d hdmem
    have hdR : d < R := Finset.mem_range.mp hdmem
    rw [hypergeometricGatewayMiss_eq_symmetricChoose R 1 d (by omega)]
    simp only [Nat.choose_one_right]
    have hcast : ((R - d : Nat) : ℝ) = (R : ℝ) - d := by
      rw [Nat.cast_sub hdR.le]
    rw [hcast]
    have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
    field_simp
    ring
  have heq : (∑ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d *
        (1 - hypergeometricGatewayMiss R 1 d)) =
      ∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d * ((d : ℝ) / R) := by
    apply Finset.sum_congr rfl
    intro d hdmem
    rw [hpoint d hdmem]
  rw [heq]
  have hdiv : (∑ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d * ((d : ℝ) / R)) =
      (∑ d ∈ Finset.range R,
        cappedZipfDegreeMass a R d * (d : ℝ)) / R := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hdmem
    ring
  rw [hdiv]
  have hfirst := cappedZipfDegreeFirstMoment_eq a R hR
  rw [show (∑ d ∈ Finset.range R,
      cappedZipfDegreeMass a R d * (d : ℝ)) = windowZipfMean a R by
    simpa only [mul_comm] using hfirst]

noncomputable def sourcePrivateAvoidanceFactor
    (a : ℝ) (R k : Nat) : ℝ :=
  ∑ d ∈ Finset.range R,
    specifiedEdgeDegreeMass a R d *
      hypergeometricGatewayMiss (R - 1) (k - 1) (d - 1)

/-- The mixed private-gateway mass is one ordinary gateway incidence times an
exact size-biased avoidance factor. -/
theorem sourcePrivateGatewayMass_eq_hit_mul_avoidance
    (a : ℝ) {R k : Nat} (ha : 1 < a) (hR : 2 ≤ R)
    (hk : 1 ≤ k) (hkR : k ≤ R) (hmean : windowZipfMean a R ≠ 0) :
    sourcePrivateGatewayMass a R k =
      powerLawMoleculeGatewayHit a R 1 *
        sourcePrivateAvoidanceFactor a R k := by
  rw [sourcePrivateGatewayMass, sourcePrivateAvoidanceFactor,
    powerLawMoleculeGatewayHit_one_eq_mean_div a R ha hR,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdR : d < R := Finset.mem_range.mp hdmem
  by_cases hd0 : d = 0
  · subst d
    simp [privateGatewayDegreeProbability, specifiedEdgeDegreeMass]
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    rw [privateGatewayDegreeProbability_eq_hit_mul_miss hk hkR hd hdR.le,
      hypergeometricContain_eq_symmetricChoose R 1 d hd hdR.le]
    simp only [Nat.choose_one_right, specifiedEdgeDegreeMass]
    have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast (by omega : R ≠ 0)
    field_simp [hmean, hR0]

theorem sourcePrivateAvoidanceFactor_nonneg_le_one
    (a : ℝ) {R k : Nat} (ha : 1 < a) (hR : 2 ≤ R)
    (hmean : 0 < windowZipfMean a R) :
    0 ≤ sourcePrivateAvoidanceFactor a R k ∧
      sourcePrivateAvoidanceFactor a R k ≤ 1 := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  have hweight : ∀ d ∈ Finset.range R,
      0 ≤ specifiedEdgeDegreeMass a R d := fun d _ =>
    specifiedEdgeDegreeMass_nonneg a R d hzpos hmean
  have hmiss : ∀ d ∈ Finset.range R,
      0 ≤ hypergeometricGatewayMiss (R - 1) (k - 1) (d - 1) ∧
        hypergeometricGatewayMiss (R - 1) (k - 1) (d - 1) ≤ 1 := by
    intro d hd
    apply hypergeometricGatewayMiss_nonneg_le_one
    have hdR : d < R := Finset.mem_range.mp hd
    omega
  rw [sourcePrivateAvoidanceFactor]
  constructor
  · exact Finset.sum_nonneg fun d hd =>
      mul_nonneg (hweight d hd) (hmiss d hd).1
  · rw [← specifiedEdgeDegreeMass_sum_eq_one a R hR hmean.ne']
    exact Finset.sum_le_sum fun d hd =>
      mul_le_of_le_one_right (hweight d hd) (hmiss d hd).2

/-- Requiring a gateway to be private can only reduce its one-incidence mass. -/
theorem sourcePrivateGatewayMass_le_gatewayHit
    (a : ℝ) {R k : Nat} (ha : 1 < a) (hR : 2 ≤ R)
    (hk : 1 ≤ k) (hkR : k ≤ R) (hmean : 0 < windowZipfMean a R) :
    sourcePrivateGatewayMass a R k ≤ powerLawMoleculeGatewayHit a R 1 := by
  rw [sourcePrivateGatewayMass_eq_hit_mul_avoidance
    a ha hR hk hkR hmean.ne']
  have hhit := powerLawMoleculeGatewayHit_nonneg_le_one a R 1 ha hR
  exact mul_le_of_le_one_right hhit.1
    (sourcePrivateAvoidanceFactor_nonneg_le_one a ha hR hmean).2

/-- Independent source degrees turn the exact fixed-degree private-gateway
product into the `k`th power of a single mixed factor. -/
theorem sourcePrivateGatewayDegreeMixture_eq_pow
    (a : ℝ) (R k : Nat) :
    (∑ degree ∈ Fintype.piFinset
        (fun _ : Fin k => Finset.range R),
      ∏ i, cappedZipfDegreeMass a R (degree i) *
        privateGatewayDegreeProbability R k (degree i)) =
      sourcePrivateGatewayMass a R k ^ k := by
  rw [sourcePrivateGatewayMass]
  exact (Finset.sum_pow' (Finset.range R)
    (fun d => cappedZipfDegreeMass a R d *
      privateGatewayDegreeProbability R k d) k).symm

end

end PowerLawSmallRAF

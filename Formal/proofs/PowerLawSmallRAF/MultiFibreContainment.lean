import proofs.PowerLawSmallRAF.FixedSizeFibreCertificates

namespace PowerLawSmallRAF

abbrev FixedSizeFibreConfig (R d k : Nat) :=
  Fin k → FixedSizeFibre R d

def assignedRequired {R k : Nat} (required : Finset (Fin R))
    (assignment : ↥required → Fin k) (i : Fin k) : Finset (Fin R) :=
  ((Finset.univ.filter fun x : ↥required => assignment x = i).image
    fun x => x.1)

theorem card_assignedRequired {R k : Nat} (required : Finset (Fin R))
    (assignment : ↥required → Fin k) (i : Fin k) :
    (assignedRequired required assignment i).card =
      (Finset.univ.filter fun x : ↥required => assignment x = i).card := by
  rw [assignedRequired, Finset.card_image_of_injective]
  intro x y h
  exact Subtype.ext h

theorem sum_card_assignedRequired {R k : Nat} (required : Finset (Fin R))
    (assignment : ↥required → Fin k) :
    ∑ i : Fin k, (assignedRequired required assignment i).card = required.card := by
  simp_rw [card_assignedRequired]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset ↥required))
    (t := (Finset.univ : Finset (Fin k)))
    (f := assignment) (by simp)
  simpa using h.symm

def fixedAssignmentLayer {R d k : Nat} (required : Finset (Fin R))
    (assignment : ↥required → Fin k) :
    Finset (FixedSizeFibreConfig R d k) :=
  Fintype.piFinset fun i : Fin k =>
    Finset.univ.filter
      (fixedSizeFibreContains (d := d) (assignedRequired required assignment i))

def multiFibreContainmentCertificateEvent {R d k : Nat}
    (required : Finset (Fin R)) : Finset (FixedSizeFibreConfig R d k) :=
  (Finset.univ : Finset (↥required → Fin k)).biUnion fun assignment =>
    fixedAssignmentLayer required assignment

theorem mem_multiFibreContainmentCertificateEvent_of_subset_union
    {R d k : Nat} (required : Finset (Fin R))
    (config : FixedSizeFibreConfig R d k)
    (hcontain : ∀ x ∈ required, ∃ i : Fin k, x ∈ (config i).1) :
    config ∈ multiFibreContainmentCertificateEvent required := by
  classical
  let assignment : ↥required → Fin k := fun x =>
    Classical.choose (hcontain x.1 x.2)
  have hassignment : ∀ x : ↥required,
      x.1 ∈ (config (assignment x)).1 := fun x =>
    Classical.choose_spec (hcontain x.1 x.2)
  simp only [multiFibreContainmentCertificateEvent, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨assignment, ?_⟩
  simp only [fixedAssignmentLayer, Fintype.mem_piFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro i x hx
  rw [assignedRequired, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyi : assignment y = i := (Finset.mem_filter.mp hy).2
  simpa [hyi] using hassignment y

theorem hypergeometricContain_le_common_power
    (R q d t : Nat) (htq : t ≤ q) (hqd : q ≤ d) (hdR : d ≤ R) :
    hypergeometricContain R t d ≤
      ((d : ℝ) / (R - q + 1 : Nat)) ^ t := by
  have htR : t ≤ R := htq.trans (hqd.trans hdR)
  have hbase := hypergeometricContain_le_power R t d
    (htq.trans hqd) hdR htR
  refine hbase.trans ?_
  apply pow_le_pow_left₀ (by positivity)
  have hdenT : (0 : ℝ) < (R - t + 1 : Nat) := by positivity
  have hdenQ : (0 : ℝ) < (R - q + 1 : Nat) := by positivity
  apply (div_le_div_iff₀ hdenT hdenQ).2
  have hden : ((R - q + 1 : Nat) : ℝ) ≤ (R - t + 1 : Nat) := by
    exact_mod_cast (by omega : R - q + 1 ≤ R - t + 1)
  exact mul_le_mul_of_nonneg_left hden (by positivity)

theorem fixedAssignmentLayer_uniformMass_le
    {R d k q : Nat} (required : Finset (Fin R)) (hcard : required.card = q)
    (assignment : ↥required → Fin k) (hqd : q ≤ d) (hdR : d ≤ R) :
    ((fixedAssignmentLayer (d := d) required assignment).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  let base : ℝ := (d : ℝ) / (R - q + 1 : Nat)
  have hchoose : 0 < Nat.choose R d := Nat.choose_pos hdR
  have hfactor : ∀ i : Fin k,
      (((Finset.univ.filter (fixedSizeFibreContains (d := d)
        (assignedRequired required assignment i))).card : Nat) : ℝ) /
          Nat.choose R d ≤ base ^ (assignedRequired required assignment i).card := by
    intro i
    have hti : (assignedRequired required assignment i).card ≤ q := by
      rw [card_assignedRequired, ← hcard]
      have hle := Finset.card_filter_le
        (Finset.univ : Finset ↥required)
        (fun x : ↥required => assignment x = i)
      simpa using hle
    rw [← card_fixedSizeFibre R d,
      fixedSizeFibre_containing_fraction
        (assignedRequired required assignment i) rfl (hti.trans hqd)]
    exact hypergeometricContain_le_common_power R q d _ hti hqd hdR
  have hprod := Finset.prod_le_prod (fun i hi => by positivity)
    (fun i hi => hfactor i) (s := (Finset.univ : Finset (Fin k)))
  rw [fixedAssignmentLayer, Fintype.card_piFinset, Fintype.card_pi,
    Finset.prod_const]
  rw [Nat.cast_prod, Nat.cast_pow, Finset.card_univ, Fintype.card_fin]
  push_cast at hprod
  have hratio : ((∏ i : Fin k,
      ((Finset.univ.filter (fixedSizeFibreContains (d := d)
        (assignedRequired required assignment i))).card : ℝ)) /
        (Nat.choose R d : ℝ) ^ k) =
      ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := d)
          (assignedRequired required assignment i))).card : ℝ) /
            Nat.choose R d) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [card_fixedSizeFibre, hratio]
  calc
    ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := d)
          (assignedRequired required assignment i))).card : ℝ) /
            Nat.choose R d) ≤
      ∏ i : Fin k, base ^ (assignedRequired required assignment i).card := hprod
    _ = base ^ q := by
      rw [Finset.prod_pow_eq_pow_sum, sum_card_assignedRequired, hcard]
    _ = (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := rfl

theorem multiFibreContainmentCertificateEvent_uniformMass_le
    {R d k q : Nat} (required : Finset (Fin R)) (hcard : required.card = q)
    (hqd : q ≤ d) (hdR : d ≤ R) :
    ((multiFibreContainmentCertificateEvent (d := d) (k := k) required).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      (k : ℝ) ^ q * (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  have hden : 0 ≤ (Fintype.card (FixedSizeFibreConfig R d k) : ℝ) := by positivity
  have hcardUnion :
      (multiFibreContainmentCertificateEvent (R := R) (d := d) (k := k)
        required).card ≤
        ∑ assignment : ↥required → Fin k,
          (fixedAssignmentLayer (R := R) (d := d) (k := k)
            required assignment).card := Finset.card_biUnion_le
    (s := (Finset.univ : Finset (↥required → Fin k)))
    (t := fun assignment => fixedAssignmentLayer required assignment)
  calc
    ((multiFibreContainmentCertificateEvent (d := d) (k := k) required).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      ((∑ assignment : ↥required → Fin k,
        (fixedAssignmentLayer required assignment).card : Nat) : ℝ) /
          Fintype.card (FixedSizeFibreConfig R d k) := by
      exact div_le_div_of_nonneg_right (by
        exact_mod_cast hcardUnion) hden
    _ = ∑ assignment : ↥required → Fin k,
        ((fixedAssignmentLayer required assignment).card : ℝ) /
          Fintype.card (FixedSizeFibreConfig R d k) := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ _assignment : ↥required → Fin k,
        (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      apply Finset.sum_le_sum
      intro assignment ha
      exact fixedAssignmentLayer_uniformMass_le required hcard assignment hqd hdR
    _ = (k : ℝ) ^ q * (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, hcard, nsmul_eq_mul]
      push_cast
      rfl

/-! Gateway-conditioned source fibres use different enumerations of their
nongateway catalogues.  The mapped variant below permits one injective channel
encoding per fibre while retaining the same assignment-counting bound. -/

def mappedAssignedRequired {α : Type*} [Fintype α] [DecidableEq α]
    {R k : Nat} (required : Finset α) (assignment : ↥required → Fin k)
    (channel : Fin k → α → Fin R) (i : Fin k) : Finset (Fin R) :=
  (Finset.univ.filter fun x : ↥required => assignment x = i).image
    fun x => channel i x.1

theorem card_mappedAssignedRequired {α : Type*} [Fintype α] [DecidableEq α]
    {R k : Nat} (required : Finset α) (assignment : ↥required → Fin k)
    (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i)) (i : Fin k) :
    (mappedAssignedRequired required assignment channel i).card =
      (Finset.univ.filter fun x : ↥required => assignment x = i).card := by
  rw [mappedAssignedRequired, Finset.card_image_of_injective]
  intro x y h
  apply Subtype.ext
  exact hchannel i h

theorem sum_card_mappedAssignedRequired
    {α : Type*} [Fintype α] [DecidableEq α] {R k : Nat}
    (required : Finset α) (assignment : ↥required → Fin k)
    (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i)) :
    ∑ i : Fin k,
      (mappedAssignedRequired required assignment channel i).card =
        required.card := by
  simp_rw [card_mappedAssignedRequired required assignment channel hchannel]
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset ↥required))
    (t := (Finset.univ : Finset (Fin k)))
    (f := assignment) (by simp)
  simpa using h.symm

def mappedFixedAssignmentLayer
    {α : Type*} [Fintype α] [DecidableEq α] {R d k : Nat}
    (required : Finset α) (assignment : ↥required → Fin k)
    (channel : Fin k → α → Fin R) :
    Finset (FixedSizeFibreConfig R d k) :=
  Fintype.piFinset fun i : Fin k =>
    Finset.univ.filter
      (fixedSizeFibreContains
        (mappedAssignedRequired required assignment channel i))

def mappedMultiFibreContainmentCertificateEvent
    {α : Type*} [Fintype α] [DecidableEq α] {R d k : Nat}
    (required : Finset α) (channel : Fin k → α → Fin R) :
    Finset (FixedSizeFibreConfig R d k) :=
  (Finset.univ : Finset (↥required → Fin k)).biUnion fun assignment =>
    mappedFixedAssignmentLayer required assignment channel

theorem mem_mappedMultiFibreContainmentCertificateEvent_of_covered
    {α : Type*} [Fintype α] [DecidableEq α] {R d k : Nat}
    (required : Finset α) (channel : Fin k → α → Fin R)
    (config : FixedSizeFibreConfig R d k)
    (hcover : ∀ x ∈ required, ∃ i : Fin k, channel i x ∈ (config i).1) :
    config ∈ mappedMultiFibreContainmentCertificateEvent required channel := by
  classical
  let assignment : ↥required → Fin k := fun x =>
    Classical.choose (hcover x.1 x.2)
  have hassignment : ∀ x : ↥required,
      channel (assignment x) x.1 ∈ (config (assignment x)).1 := fun x =>
    Classical.choose_spec (hcover x.1 x.2)
  simp only [mappedMultiFibreContainmentCertificateEvent,
    Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨assignment, ?_⟩
  simp only [mappedFixedAssignmentLayer, Fintype.mem_piFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  intro i x hx
  rw [mappedAssignedRequired, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyi : assignment y = i := (Finset.mem_filter.mp hy).2
  subst i
  exact hassignment y

theorem mappedFixedAssignmentLayer_uniformMass_le
    {α : Type*} [Fintype α] [DecidableEq α] {R d k q : Nat}
    (required : Finset α) (hcard : required.card = q)
    (assignment : ↥required → Fin k) (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i))
    (hqd : q ≤ d) (hdR : d ≤ R) :
    ((mappedFixedAssignmentLayer (d := d) required assignment channel).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  let base : ℝ := (d : ℝ) / (R - q + 1 : Nat)
  have hfactor : ∀ i : Fin k,
      (((Finset.univ.filter (fixedSizeFibreContains (d := d)
        (mappedAssignedRequired required assignment channel i))).card : Nat) : ℝ) /
          Nat.choose R d ≤
        base ^ (mappedAssignedRequired required assignment channel i).card := by
    intro i
    have hti : (mappedAssignedRequired required assignment channel i).card ≤ q := by
      rw [card_mappedAssignedRequired required assignment channel hchannel, ← hcard]
      have hle := Finset.card_filter_le
        (Finset.univ : Finset ↥required)
        (fun x : ↥required => assignment x = i)
      simpa using hle
    rw [← card_fixedSizeFibre R d,
      fixedSizeFibre_containing_fraction
        (mappedAssignedRequired required assignment channel i)
        rfl (hti.trans hqd)]
    exact hypergeometricContain_le_common_power R q d _ hti hqd hdR
  have hprod := Finset.prod_le_prod (fun i hi => by positivity)
    (fun i hi => hfactor i) (s := (Finset.univ : Finset (Fin k)))
  rw [mappedFixedAssignmentLayer, Fintype.card_piFinset, Fintype.card_pi,
    Finset.prod_const]
  rw [Nat.cast_prod, Nat.cast_pow, Finset.card_univ, Fintype.card_fin]
  push_cast at hprod
  have hratio : ((∏ i : Fin k,
      ((Finset.univ.filter (fixedSizeFibreContains (d := d)
        (mappedAssignedRequired required assignment channel i))).card : ℝ)) /
        (Nat.choose R d : ℝ) ^ k) =
      ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := d)
          (mappedAssignedRequired required assignment channel i))).card : ℝ) /
            Nat.choose R d) := by
    rw [Finset.prod_div_distrib]
    simp
  rw [card_fixedSizeFibre, hratio]
  calc
    ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := d)
          (mappedAssignedRequired required assignment channel i))).card : ℝ) /
            Nat.choose R d) ≤
      ∏ i : Fin k,
        base ^ (mappedAssignedRequired required assignment channel i).card := hprod
    _ = base ^ q := by
      rw [Finset.prod_pow_eq_pow_sum,
        sum_card_mappedAssignedRequired required assignment channel hchannel,
        hcard]
    _ = (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := rfl

theorem mappedMultiFibreContainmentCertificateEvent_uniformMass_le
    {α : Type*} [Fintype α] [DecidableEq α] {R d k q : Nat}
    (required : Finset α) (hcard : required.card = q)
    (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i))
    (hqd : q ≤ d) (hdR : d ≤ R) :
    ((mappedMultiFibreContainmentCertificateEvent (d := d)
      (k := k) required channel).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      (k : ℝ) ^ q * (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  have hden : 0 ≤ (Fintype.card (FixedSizeFibreConfig R d k) : ℝ) := by
    positivity
  have hcardUnion :
      (mappedMultiFibreContainmentCertificateEvent (R := R) (d := d)
        (k := k) required channel).card ≤
        ∑ assignment : ↥required → Fin k,
          (mappedFixedAssignmentLayer (R := R) (d := d) (k := k)
            required assignment channel).card := Finset.card_biUnion_le
  calc
    ((mappedMultiFibreContainmentCertificateEvent (d := d)
      (k := k) required channel).card : ℝ) /
        Fintype.card (FixedSizeFibreConfig R d k) ≤
      ((∑ assignment : ↥required → Fin k,
        (mappedFixedAssignmentLayer required assignment channel).card : Nat) : ℝ) /
          Fintype.card (FixedSizeFibreConfig R d k) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcardUnion) hden
    _ = ∑ assignment : ↥required → Fin k,
        ((mappedFixedAssignmentLayer required assignment channel).card : ℝ) /
          Fintype.card (FixedSizeFibreConfig R d k) := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ _assignment : ↥required → Fin k,
        (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      apply Finset.sum_le_sum
      intro assignment ha
      exact mappedFixedAssignmentLayer_uniformMass_le required hcard assignment
        channel hchannel hqd hdR
    _ = (k : ℝ) ^ q * (((d : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, hcard, nsmul_eq_mul]
      push_cast
      rfl

/-! The source law gives the different hubs independent, generally unequal,
degrees.  The variable-degree form is dominated by a common upper cutoff `D`.
-/

abbrev VariableFixedSizeFibreConfig {k : Nat} (R : Nat)
    (degree : Fin k → Nat) :=
  ∀ i : Fin k, FixedSizeFibre R (degree i)

def mappedVariableAssignmentLayer
    {α : Type*} [Fintype α] [DecidableEq α] {R k : Nat}
    (degree : Fin k → Nat) (required : Finset α)
    (assignment : ↥required → Fin k) (channel : Fin k → α → Fin R) :
    Finset (VariableFixedSizeFibreConfig R degree) :=
  Fintype.piFinset fun i : Fin k =>
    Finset.univ.filter (fixedSizeFibreContains (d := degree i)
      (mappedAssignedRequired required assignment channel i))

def mappedVariableContainmentCertificateEvent
    {α : Type*} [Fintype α] [DecidableEq α] {R k : Nat}
    (degree : Fin k → Nat) (required : Finset α)
    (channel : Fin k → α → Fin R) :
    Finset (VariableFixedSizeFibreConfig R degree) :=
  (Finset.univ : Finset (↥required → Fin k)).biUnion fun assignment =>
    mappedVariableAssignmentLayer degree required assignment channel

theorem mem_mappedVariableContainmentCertificateEvent_of_covered
    {α : Type*} [Fintype α] [DecidableEq α] {R k : Nat}
    (degree : Fin k → Nat) (required : Finset α)
    (channel : Fin k → α → Fin R)
    (config : VariableFixedSizeFibreConfig R degree)
    (hcover : ∀ x ∈ required, ∃ i : Fin k, channel i x ∈ (config i).1) :
    config ∈ mappedVariableContainmentCertificateEvent degree required channel := by
  classical
  let assignment : ↥required → Fin k := fun x =>
    Classical.choose (hcover x.1 x.2)
  have hassignment : ∀ x : ↥required,
      channel (assignment x) x.1 ∈ (config (assignment x)).1 := fun x =>
    Classical.choose_spec (hcover x.1 x.2)
  simp only [mappedVariableContainmentCertificateEvent, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨assignment, ?_⟩
  simp only [mappedVariableAssignmentLayer, Fintype.mem_piFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  intro i x hx
  rw [mappedAssignedRequired, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyi : assignment y = i := (Finset.mem_filter.mp hy).2
  subst i
  exact hassignment y

theorem mappedVariableAssignmentLayer_uniformMass_le
    {α : Type*} [Fintype α] [DecidableEq α] {R k q D : Nat}
    (degree : Fin k → Nat) (required : Finset α)
    (hcard : required.card = q) (assignment : ↥required → Fin k)
    (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i))
    (hdegree : ∀ i, degree i ≤ D) (hqD : q ≤ D) (hDR : D ≤ R) :
    ((mappedVariableAssignmentLayer degree required assignment channel).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) ≤
      (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  let base : ℝ := (D : ℝ) / (R - q + 1 : Nat)
  have hdegreeR : ∀ i, degree i ≤ R := fun i => (hdegree i).trans hDR
  have hfactor : ∀ i : Fin k,
      (((Finset.univ.filter (fixedSizeFibreContains (d := degree i)
        (mappedAssignedRequired required assignment channel i))).card : Nat) : ℝ) /
          Nat.choose R (degree i) ≤
        base ^ (mappedAssignedRequired required assignment channel i).card := by
    intro i
    let req := mappedAssignedRequired required assignment channel i
    have htq : req.card ≤ q := by
      rw [card_mappedAssignedRequired required assignment channel hchannel, ← hcard]
      have hle := Finset.card_filter_le
        (Finset.univ : Finset ↥required)
        (fun x : ↥required => assignment x = i)
      simpa [req] using hle
    by_cases htd : req.card ≤ degree i
    · rw [← card_fixedSizeFibre R (degree i),
        fixedSizeFibre_containing_fraction req rfl htd]
      have htR : req.card ≤ R := htq.trans (hqD.trans hDR)
      have hraw := hypergeometricContain_le_power R req.card (degree i)
        htd (hdegreeR i) htR
      refine hraw.trans ?_
      apply pow_le_pow_left₀ (by positivity)
      calc
        (degree i : ℝ) / (R - req.card + 1 : Nat) ≤
            (D : ℝ) / (R - req.card + 1 : Nat) := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hdegree i) (by positivity)
        _ ≤ (D : ℝ) / (R - q + 1 : Nat) := by
          have hdenT : (0 : ℝ) < (R - req.card + 1 : Nat) := by positivity
          have hdenQ : (0 : ℝ) < (R - q + 1 : Nat) := by positivity
          apply (div_le_div_iff₀ hdenT hdenQ).2
          have hden : ((R - q + 1 : Nat) : ℝ) ≤
              (R - req.card + 1 : Nat) := by
            exact_mod_cast (by omega : R - q + 1 ≤ R - req.card + 1)
          exact mul_le_mul_of_nonneg_left hden (by positivity)
    · have hempty : Finset.univ.filter (fixedSizeFibreContains
          (d := degree i) req) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro fibre hfibre
        have hsubset : req ⊆ fibre.1 := (Finset.mem_filter.mp hfibre).2
        have hle := Finset.card_le_card hsubset
        rw [(Finset.mem_powersetCard.mp fibre.property).2] at hle
        exact htd hle
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, zero_div]
      positivity
  have hprod := Finset.prod_le_prod (fun i hi => by positivity)
    (fun i hi => hfactor i) (s := (Finset.univ : Finset (Fin k)))
  rw [mappedVariableAssignmentLayer, Fintype.card_piFinset,
    Fintype.card_pi]
  rw [Nat.cast_prod, Nat.cast_prod]
  push_cast at hprod
  have hratio : ((∏ i : Fin k,
      ((Finset.univ.filter (fixedSizeFibreContains (d := degree i)
        (mappedAssignedRequired required assignment channel i))).card : ℝ)) /
        ∏ i : Fin k, (Nat.choose R (degree i) : ℝ)) =
      ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := degree i)
          (mappedAssignedRequired required assignment channel i))).card : ℝ) /
            Nat.choose R (degree i)) := by
    rw [Finset.prod_div_distrib]
  rw [show (∏ i : Fin k, (Fintype.card (FixedSizeFibre R (degree i)) : ℝ)) =
      ∏ i : Fin k, (Nat.choose R (degree i) : ℝ) by
        apply Finset.prod_congr rfl
        intro i hi
        rw [card_fixedSizeFibre], hratio]
  calc
    ∏ i : Fin k,
        (((Finset.univ.filter (fixedSizeFibreContains (d := degree i)
          (mappedAssignedRequired required assignment channel i))).card : ℝ) /
            Nat.choose R (degree i)) ≤
      ∏ i : Fin k,
        base ^ (mappedAssignedRequired required assignment channel i).card := hprod
    _ = base ^ q := by
      rw [Finset.prod_pow_eq_pow_sum,
        sum_card_mappedAssignedRequired required assignment channel hchannel,
        hcard]
    _ = (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := rfl

theorem mappedVariableContainmentCertificateEvent_uniformMass_le
    {α : Type*} [Fintype α] [DecidableEq α] {R k q D : Nat}
    (degree : Fin k → Nat) (required : Finset α)
    (hcard : required.card = q) (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i))
    (hdegree : ∀ i, degree i ≤ D) (hqD : q ≤ D) (hDR : D ≤ R) :
    ((mappedVariableContainmentCertificateEvent degree required channel).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) ≤
      (k : ℝ) ^ q * (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := by
  have hden : 0 ≤ (Fintype.card
      (VariableFixedSizeFibreConfig R degree) : ℝ) := by positivity
  have hcardUnion :
      (mappedVariableContainmentCertificateEvent degree required channel).card ≤
        ∑ assignment : ↥required → Fin k,
          (mappedVariableAssignmentLayer degree required assignment channel).card :=
    Finset.card_biUnion_le
  calc
    ((mappedVariableContainmentCertificateEvent degree required channel).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) ≤
      ((∑ assignment : ↥required → Fin k,
        (mappedVariableAssignmentLayer degree required assignment channel).card : Nat) : ℝ) /
          Fintype.card (VariableFixedSizeFibreConfig R degree) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcardUnion) hden
    _ = ∑ assignment : ↥required → Fin k,
        ((mappedVariableAssignmentLayer degree required assignment channel).card : ℝ) /
          Fintype.card (VariableFixedSizeFibreConfig R degree) := by
      push_cast
      rw [Finset.sum_div]
    _ ≤ ∑ _assignment : ↥required → Fin k,
        (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      apply Finset.sum_le_sum
      intro assignment ha
      exact mappedVariableAssignmentLayer_uniformMass_le degree required hcard
        assignment channel hchannel hdegree hqD hDR
    _ = (k : ℝ) ^ q * (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, hcard, nsmul_eq_mul]
      push_cast
      rfl

theorem mappedVariableContainmentCertificateEvent_coarse_le
    {α : Type*} [Fintype α] [DecidableEq α]
    {R k q D s : Nat} (degree : Fin k → Nat) (required : Finset α)
    (hcard : required.card = q) (channel : Fin k → α → Fin R)
    (hchannel : ∀ i, Function.Injective (channel i))
    (hdegree : ∀ i, degree i ≤ D) (hqD : q ≤ D) (hDR : D ≤ R)
    (hqs : q ≤ s) (hskq : s - k ≤ q)
    (hbase : (k : ℝ) * D / (R - s + 1 : Nat) ≤ 1) :
    ((mappedVariableContainmentCertificateEvent degree required channel).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) ≤
      ((k : ℝ) * D / (R - s + 1 : Nat)) ^ (s - k) := by
  let base : ℝ := (k : ℝ) * D / (R - s + 1 : Nat)
  have hfinite := mappedVariableContainmentCertificateEvent_uniformMass_le
    degree required hcard channel hchannel hdegree hqD hDR
  calc
    ((mappedVariableContainmentCertificateEvent degree required channel).card : ℝ) /
        Fintype.card (VariableFixedSizeFibreConfig R degree) ≤
      (k : ℝ) ^ q * (((D : ℝ) / (R - q + 1 : Nat)) ^ q) := hfinite
    _ = ((k : ℝ) * D / (R - q + 1 : Nat)) ^ q := by
      rw [mul_div_assoc, mul_pow]
    _ ≤ base ^ q := by
      apply pow_le_pow_left₀ (by positivity)
      dsimp only [base]
      have hdenQ : (0 : ℝ) < (R - q + 1 : Nat) := by positivity
      have hdenS : (0 : ℝ) < (R - s + 1 : Nat) := by positivity
      apply (div_le_div_iff₀ hdenQ hdenS).2
      have hden : ((R - s + 1 : Nat) : ℝ) ≤ (R - q + 1 : Nat) := by
        exact_mod_cast (by omega : R - s + 1 ≤ R - q + 1)
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ base ^ (s - k) := by
      exact pow_le_pow_of_le_one (by positivity) hbase hskq

end PowerLawSmallRAF

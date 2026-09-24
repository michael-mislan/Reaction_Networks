import proofs.ThermoCoreCompatibility.Direction
import proofs.ThermoCoreCompatibility.Toric
import proofs.ThermoCoreCompatibility.Examples.PaperIncompatiblePair

/-! A source-level candidate refuting Strong Compatibility by a pure current-
magnitude obstruction. Two autocatalytic triangles share `A -> B`; the private
right currents have barriers ten times larger. -/

namespace ThermoCoreCompatibility.MagnitudePair

open scoped BigOperators
open ThermoCoreCompatibility

abbrev Species := Fin 4
namespace Species
@[simp] def A : Species := 0
@[simp] def B : Species := 1
@[simp] def C : Species := 2
@[simp] def D : Species := 3
end Species

abbrev Reaction := Fin 5
namespace Reaction
@[simp] def r0 : Reaction := 0
@[simp] def r1 : Reaction := 1
@[simp] def r2 : Reaction := 2
@[simp] def r3 : Reaction := 3
@[simp] def r4 : Reaction := 4
end Reaction

inductive Core | left | right
  deriving DecidableEq, Fintype

def reactant (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 0 | 1, 1 | 2, 2 | 3, 1 | 4, 3 => 1
  | _, _ => 0

def product (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 1 | 1, 2 | 3, 3 => 1
  | 2, 0 | 4, 0 => 2
  | _, _ => 0

def barrier (r : Reaction) : ℝ := if r.val < 3 then 1 else 10

theorem barrier_pos (r : Reaction) : 0 < barrier r := by
  fin_cases r <;> norm_num [barrier]

def network : ReversibleCRN Species Reaction where
  reactant := reactant
  product := product
  barrier := barrier
  barrier_pos := barrier_pos

def leftMotif : Motif network where
  species := {.A, .B, .C}
  reactions := {.r0, .r1, .r2}

def rightMotif : Motif network where
  species := {.A, .B, .D}
  reactions := {.r0, .r3, .r4}

noncomputable def commonFlow (r : Reaction) : ℝ :=
  match r.val with
  | 0 => 1
  | 1 | 3 => 4 / 5
  | _ => 3 / 5

private theorem sum_left {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r1, .r2} : Finset Reaction), f r = f .r0 + f .r1 + f .r2 := by
  simp [Finset.sum_insert, add_assoc]

private theorem sum_right {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r3, .r4} : Finset Reaction), f r = f .r0 + f .r3 + f .r4 := by
  simp [Finset.sum_insert, add_assoc]

private theorem sum_over_reactions (S : Finset Reaction) (f : Reaction → ℝ) :
    ∑ r ∈ S, f r = ∑ r : Reaction, (if r ∈ S then f r else 0) := by
  calc
    ∑ r ∈ S, f r = ∑ r ∈ S, (if r ∈ S then f r else 0) := by simp
    _ = ∑ r ∈ Finset.univ, (if r ∈ S then f r else 0) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro r _ hr
      simp [hr]

private theorem balanceA (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, (network.stoich .A r : ℝ) * v r =
      (if .r0 ∈ S then -v .r0 else 0) + (if .r2 ∈ S then 2 * v .r2 else 0) +
        (if .r4 ∈ S then 2 * v .r4 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]
  simp only [show Fin.succ (Fin.succ (2 : Fin 3)) = (4 : Reaction) by decide]
  exact (add_assoc _ _ _).symm

private theorem balanceB (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, (network.stoich .B r : ℝ) * v r =
      (if .r0 ∈ S then v .r0 else 0) + (if .r1 ∈ S then -v .r1 else 0) +
        (if .r3 ∈ S then -v .r3 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]
  simp only [show Fin.succ (2 : Fin 4) = (3 : Reaction) by decide]
  exact (add_assoc _ _ _).symm

private theorem balanceC (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, (network.stoich .C r : ℝ) * v r =
      (if .r1 ∈ S then v .r1 else 0) + (if .r2 ∈ S then -v .r2 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]

private theorem balanceD (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, (network.stoich .D r : ℝ) * v r =
      (if .r3 ∈ S then v .r3 else 0) + (if .r4 ∈ S then -v .r4 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]
  simp only [show Fin.succ (2 : Fin 4) = (3 : Reaction) by decide,
    show Fin.succ (Fin.succ (2 : Fin 3)) = (4 : Reaction) by decide]

private theorem triangle_support_complete
    (m0 m1 m2 : Prop) [Decidable m0] [Decidable m1] [Decidable m2]
    (v0 v1 v2 : ℝ) (hne : m0 ∨ m1 ∨ m2)
    (p0a : m0 → 0 < (if m0 then -v0 else 0) + (if m2 then 2 * v2 else 0))
    (p0b : m0 → 0 < (if m0 then v0 else 0) + (if m1 then -v1 else 0))
    (p1a : m1 → 0 < (if m0 then v0 else 0) + (if m1 then -v1 else 0))
    (p1b : m1 → 0 < (if m1 then v1 else 0) + (if m2 then -v2 else 0))
    (p2a : m2 → 0 < (if m1 then v1 else 0) + (if m2 then -v2 else 0))
    (p2b : m2 → 0 < (if m0 then -v0 else 0) + (if m2 then 2 * v2 else 0)) :
    m0 ∧ m1 ∧ m2 := by
  by_cases h0 : m0 <;> by_cases h1 : m1 <;> by_cases h2 : m2 <;>
    simp_all <;> linarith

theorem left_sideIncident : leftMotif.SideIncident := by
  constructor
  · exact ⟨.A, by simp [leftMotif]⟩
  constructor
  · exact ⟨.r0, by simp [leftMotif]⟩
  intro r hr
  fin_cases r <;> simp_all [leftMotif, network, reactant, product]

theorem right_sideIncident : rightMotif.SideIncident := by
  constructor
  · exact ⟨.A, by simp [rightMotif]⟩
  constructor
  · exact ⟨.r0, by simp [rightMotif]⟩
  intro r hr
  fin_cases r <;> simp_all [rightMotif, network, reactant, product]

theorem left_productive : leftMotif.Productive commonFlow := by
  intro s hs
  fin_cases s
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]
  · simp [leftMotif] at hs

theorem right_productive : rightMotif.Productive commonFlow := by
  intro s hs
  fin_cases s
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]
  · simp [rightMotif] at hs
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]

private theorem left_reactions_complete
    (small : Motif network) (hsub : small.reactions ⊆ leftMotif.reactions)
    (hauto : small.IsAutocatalyticMotif) : small.reactions = leftMotif.reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have hp := hside.2.2
  have h0end (h0 : Reaction.r0 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hp .r0 h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h1end (h1 : Reaction.r1 ∈ small.reactions) :
      Species.B ∈ small.species ∧ Species.C ∈ small.species := by
    rcases hp .r1 h1 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h2end (h2 : Reaction.r2 ∈ small.reactions) :
      Species.C ∈ small.species ∧ Species.A ∈ small.species := by
    rcases hp .r2 h2 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h3 : (3 : Reaction) ∉ small.reactions := by
    intro h; have := hsub h; simp [leftMotif] at this
  have h4 : (4 : Reaction) ∉ small.reactions := by
    intro h; have := hsub h; simp [leftMotif] at this
  have hne : Reaction.r0 ∈ small.reactions ∨ Reaction.r1 ∈ small.reactions ∨
      Reaction.r2 ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [leftMotif]
  have p0a := fun h => hprod .A (h0end h).1
  have p0b := fun h => hprod .B (h0end h).2
  have p1a := fun h => hprod .B (h1end h).1
  have p1b := fun h => hprod .C (h1end h).2
  have p2a := fun h => hprod .C (h2end h).1
  have p2b := fun h => hprod .A (h2end h).2
  rw [balanceA] at p0a p2b
  rw [balanceB] at p0b p1a
  rw [balanceC] at p1b p2a
  simp [h4] at p0a p2b
  simp [h3] at p0b p1a
  have hall := triangle_support_complete
    (Reaction.r0 ∈ small.reactions) (Reaction.r1 ∈ small.reactions)
    (Reaction.r2 ∈ small.reactions) (v .r0) (v .r1) (v .r2) hne
    p0a p0b p1a p1b p2a p2b
  ext r
  fin_cases r <;> simp_all [leftMotif]

private theorem left_species_complete
    (small : Motif network) (hsp : small.species ⊆ leftMotif.species)
    (hreac : small.reactions = leftMotif.reactions) (hside : small.SideIncident) :
    small.species = leftMotif.species := by
  apply Finset.Subset.antisymm hsp
  intro s hs
  fin_cases s
  · rcases (hside.2.2 .r0 (by rw [hreac]; simp [leftMotif])).1 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, reactant] at h
    exact ht
  · rcases (hside.2.2 .r0 (by rw [hreac]; simp [leftMotif])).2 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, product] at h
    exact ht
  · rcases (hside.2.2 .r1 (by rw [hreac]; simp [leftMotif])).2 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, product] at h
    exact ht
  · simp [leftMotif] at hs

theorem left_isPAC : leftMotif.IsPAC := by
  constructor
  · exact ⟨left_sideIncident, commonFlow, left_productive⟩
  intro small hstrict hauto
  have hreac := left_reactions_complete small hstrict.2.1 hauto
  have hspecies := left_species_complete small hstrict.1 hreac hauto.1
  rcases hstrict.2.2 with hs | hr
  · exact hs hspecies
  · exact hr hreac

private theorem right_reactions_complete
    (small : Motif network) (hsub : small.reactions ⊆ rightMotif.reactions)
    (hauto : small.IsAutocatalyticMotif) : small.reactions = rightMotif.reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have hp := hside.2.2
  have h0end (h0 : Reaction.r0 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hp .r0 h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h3end (h3 : Reaction.r3 ∈ small.reactions) :
      Species.B ∈ small.species ∧ Species.D ∈ small.species := by
    rcases hp .r3 h3 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h4end (h4 : Reaction.r4 ∈ small.reactions) :
      Species.D ∈ small.species ∧ Species.A ∈ small.species := by
    rcases hp .r4 h4 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h1 : (1 : Reaction) ∉ small.reactions := by
    intro h; have := hsub h; simp [rightMotif] at this
  have h2 : (2 : Reaction) ∉ small.reactions := by
    intro h; have := hsub h; simp [rightMotif] at this
  have hne : Reaction.r0 ∈ small.reactions ∨ Reaction.r3 ∈ small.reactions ∨
      Reaction.r4 ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [rightMotif]
  have p0a := fun h => hprod .A (h0end h).1
  have p0b := fun h => hprod .B (h0end h).2
  have p3a := fun h => hprod .B (h3end h).1
  have p3b := fun h => hprod .D (h3end h).2
  have p4a := fun h => hprod .D (h4end h).1
  have p4b := fun h => hprod .A (h4end h).2
  rw [balanceA] at p0a p4b
  rw [balanceB] at p0b p3a
  rw [balanceD] at p3b p4a
  simp [h2] at p0a p4b
  simp [h1] at p0b p3a
  have hall := triangle_support_complete
    (Reaction.r0 ∈ small.reactions) (Reaction.r3 ∈ small.reactions)
    (Reaction.r4 ∈ small.reactions) (v .r0) (v .r3) (v .r4) hne
    p0a p0b p3a p3b p4a p4b
  ext r
  fin_cases r <;> simp_all [rightMotif]

private theorem right_species_complete
    (small : Motif network) (hsp : small.species ⊆ rightMotif.species)
    (hreac : small.reactions = rightMotif.reactions) (hside : small.SideIncident) :
    small.species = rightMotif.species := by
  apply Finset.Subset.antisymm hsp
  intro s hs
  fin_cases s
  · rcases (hside.2.2 .r0 (by rw [hreac]; simp [rightMotif])).1 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, reactant] at h
    exact ht
  · rcases (hside.2.2 .r0 (by rw [hreac]; simp [rightMotif])).2 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, product] at h
    exact ht
  · simp [rightMotif] at hs
  · rcases (hside.2.2 .r3 (by rw [hreac]; simp [rightMotif])).2 with ⟨t, ht, h⟩
    fin_cases t <;> norm_num [network, product] at h
    exact ht

theorem right_isPAC : rightMotif.IsPAC := by
  constructor
  · exact ⟨right_sideIncident, commonFlow, right_productive⟩
  intro small hstrict hauto
  have hreac := right_reactions_complete small hstrict.2.1 hauto
  have hspecies := right_species_complete small hstrict.1 hreac hauto.1
  rcases hstrict.2.2 with hs | hr
  · exact hs hspecies
  · exact hr hreac

def family : CoreFamily (Core := Core) network where
  core
    | .left => leftMotif
    | .right => rightMotif
  core_isPAC
    | .left => left_isPAC
    | .right => right_isPAC
  orientation := fun _ => 1
  orientation_unit := by simp
  owner := fun r => if r.val < 3 then .left else .right
  owner_mem := by
    intro r
    fin_cases r <;> simp [leftMotif, rightMotif]

theorem family_multiPAC : family.MultiPAC := by
  refine ⟨commonFlow, ?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [family, commonFlow]
  · intro k
    cases k with
    | left => exact left_productive
    | right => exact right_productive

noncomputable def directionPotential (s : Species) : ℝ :=
  match s.val with
  | 0 => -1
  | 1 => -(3 / 2)
  | _ => -(9 / 5)

theorem family_directionCompatible : family.DirectionCompatible := by
  refine ⟨directionPotential, ?_⟩
  intro r
  fin_cases r <;>
    norm_num [CoreFamily.directionalAffinity, CoreFamily.orientedDisplacement,
      family, network, reactant, product, directionPotential, Fin.sum_univ_succ]

theorem no_common_full_realization
    (z : Species → ℝ)
    (hL : leftMotif.Productive (network.current z))
    (hR : rightMotif.Productive (network.current z)) : False := by
  have hLA := hL .A (by simp [leftMotif])
  have hLB := hL .B (by simp [leftMotif])
  have hLC := hL .C (by simp [leftMotif])
  have hRA := hR .A (by simp [rightMotif])
  have hRB := hR .B (by simp [rightMotif])
  have hRD := hR .D (by simp [rightMotif])
  simp only [leftMotif] at hLA hLB hLC
  simp only [rightMotif] at hRA hRB hRD
  rw [sum_left] at hLA hLB hLC
  rw [sum_right] at hRA hRB hRD
  norm_num [network, ReversibleCRN.stoich, reactant, product,
    ReversibleCRN.current, ReversibleCRN.complexActivity, barrier, Fin.prod_univ_succ]
    at hLA hLB hLC hRA hRB hRD
  nlinarith

theorem no_common_linearComplex_realization
    (y : Complex Species → ℝ)
    (hL : leftMotif.Productive (network.linearCurrent y))
    (hR : rightMotif.Productive (network.linearCurrent y)) : False := by
  have hLA := hL .A (by simp [leftMotif])
  have hLB := hL .B (by simp [leftMotif])
  have hLC := hL .C (by simp [leftMotif])
  have hRA := hR .A (by simp [rightMotif])
  have hRB := hR .B (by simp [rightMotif])
  have hRD := hR .D (by simp [rightMotif])
  simp only [leftMotif] at hLA hLB hLC
  simp only [rightMotif] at hRA hRB hRD
  rw [sum_left] at hLA hLB hLC
  rw [sum_right] at hRA hRB hRD
  norm_num [network, ReversibleCRN.stoich, reactant, product,
    ReversibleCRN.linearCurrent, barrier]
    at hLA hLB hLC hRA hRB hRD
  have yB1 : y (reactant (1 : Reaction)) = y (product (0 : Reaction)) := by
    congr 1; funext s; fin_cases s <;> rfl
  have yB3 : y (reactant (3 : Reaction)) = y (product (0 : Reaction)) := by
    congr 1; funext s; fin_cases s <;> rfl
  have yC : y (product (1 : Reaction)) = y (reactant (2 : Reaction)) := by
    congr 1; funext s; fin_cases s <;> rfl
  have yD : y (product (3 : Reaction)) = y (reactant (4 : Reaction)) := by
    congr 1; funext s; fin_cases s <;> rfl
  have yA2 : y (product (4 : Reaction)) = y (product (2 : Reaction)) := by
    congr 1; funext s; fin_cases s <;> rfl
  rw [yB1] at hLB hLC
  rw [yB3] at hRB hRD
  rw [yC] at hLB hLC
  rw [yD] at hRB hRD
  rw [yA2] at hRA hRD
  linarith

theorem family_not_linearComplexCompatible : ¬ family.LinearComplexCompatible := by
  rintro ⟨y, _hy, _horiented, hproductive⟩
  exact no_common_linearComplex_realization y
    (hproductive .left) (hproductive .right)

theorem family_not_multiCAC : ¬ family.MultiCAC := by
  rintro ⟨z, _hz, _horiented, hproductive⟩
  exact no_common_full_realization z (hproductive .left) (hproductive .right)

/-- A fully source-valid two-PAC family with a common productive orientation and
a strict direction potential, but no common mass-action concentration. -/
theorem strongCompatibility_counterexample :
    family.MultiPAC ∧ family.DirectionCompatible ∧ ¬ family.MultiCAC :=
  ⟨family_multiPAC, family_directionCompatible, family_not_multiCAC⟩

theorem magnitudeObstruction_is_nonToric :
    family.MultiPAC ∧ family.DirectionCompatible ∧
      ¬ family.LinearComplexCompatible :=
  ⟨family_multiPAC, family_directionCompatible,
    family_not_linearComplexCompatible⟩

end ThermoCoreCompatibility.MagnitudePair

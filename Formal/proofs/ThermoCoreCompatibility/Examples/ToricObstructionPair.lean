import proofs.ThermoCoreCompatibility.Direction
import proofs.ThermoCoreCompatibility.Toric

/-! A two-species, three-reaction obstruction at the toric layer.

The two source-minimal two-reaction PACs share `A ⇌ B`; their distinct private
reactions are `B ⇌ 2A` and `B ⇌ 3A`. Independent complex activities realize
both productive cones, but no common species activity does. -/

namespace ThermoCoreCompatibility.ToricPair

open scoped BigOperators
open ThermoCoreCompatibility

abbrev Species := Fin 2
namespace Species
@[simp] def A : Species := 0
@[simp] def B : Species := 1
end Species

abbrev Reaction := Fin 3
namespace Reaction
@[simp] def r0 : Reaction := 0
@[simp] def r1 : Reaction := 1
@[simp] def r2 : Reaction := 2
end Reaction

inductive Core | left | right
  deriving DecidableEq, Fintype

def reactant (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 0 | 1, 1 | 2, 1 => 1
  | _, _ => 0

def product (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 1 => 1
  | 1, 0 => 2
  | 2, 0 => 3
  | _, _ => 0

def barrier (r : Reaction) : ℝ := if r.val = 2 then 2 else 1

theorem barrier_pos (r : Reaction) : 0 < barrier r := by
  fin_cases r <;> norm_num [barrier]

def network : ReversibleCRN Species Reaction where
  reactant := reactant
  product := product
  barrier := barrier
  barrier_pos := barrier_pos

def leftMotif : Motif network where
  species := {.A, .B}
  reactions := {.r0, .r1}

def rightMotif : Motif network where
  species := {.A, .B}
  reactions := {.r0, .r2}

noncomputable def commonFlow (r : Reaction) : ℝ :=
  match r.val with | 0 => 1 | 1 => 3 / 4 | _ => 1 / 2

private theorem sum_left {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r1} : Finset Reaction), f r = f .r0 + f .r1 := by simp

private theorem sum_right {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r0, .r2} : Finset Reaction), f r = f .r0 + f .r2 := by simp

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
      (if .r0 ∈ S then -v .r0 else 0) +
      (if .r1 ∈ S then 2 * v .r1 else 0) +
      (if .r2 ∈ S then 3 * v .r2 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]
  ring

private theorem balanceB (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, (network.stoich .B r : ℝ) * v r =
      (if .r0 ∈ S then v .r0 else 0) +
      (if .r1 ∈ S then -v .r1 else 0) +
      (if .r2 ∈ S then -v .r2 else 0) := by
  rw [sum_over_reactions]
  simp only [Fin.sum_univ_succ]
  norm_num [network, ReversibleCRN.stoich, reactant, product]
  ring

theorem left_sideIncident : leftMotif.SideIncident := by
  refine ⟨⟨.A, by simp [leftMotif]⟩, ⟨.r0, by simp [leftMotif]⟩, ?_⟩
  intro r hr
  fin_cases r <;> simp_all [leftMotif, network, reactant, product]

theorem right_sideIncident : rightMotif.SideIncident := by
  refine ⟨⟨.A, by simp [rightMotif]⟩, ⟨.r0, by simp [rightMotif]⟩, ?_⟩
  intro r hr
  fin_cases r <;> simp_all [rightMotif, network, reactant, product]

theorem left_productive : leftMotif.Productive commonFlow := by
  intro s hs
  fin_cases s <;> simp only [leftMotif] at hs ⊢ <;> rw [sum_left] <;>
    norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]

theorem right_productive : rightMotif.Productive commonFlow := by
  intro s hs
  fin_cases s <;> simp only [rightMotif] at hs ⊢ <;> rw [sum_right] <;>
    norm_num [network, ReversibleCRN.stoich, reactant, product, commonFlow]

private theorem left_reactions_complete
    (small : Motif network) (hsub : small.reactions ⊆ leftMotif.reactions)
    (hauto : small.IsAutocatalyticMotif) : small.reactions = leftMotif.reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have h2 : Reaction.r2 ∉ small.reactions := by
    intro h; have := hsub h; simp [leftMotif] at this
  have hne : Reaction.r0 ∈ small.reactions ∨ Reaction.r1 ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [leftMotif]
  have h0end (h0 : Reaction.r0 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hside.2.2 .r0 h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hp⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hp
      exact ht
  have h1end (h1 : Reaction.r1 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hside.2.2 .r1 h1 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hp⟩⟩
    constructor
    · fin_cases t <;> norm_num [network, product] at hp
      exact ht
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
  have pA0 := fun h => hprod .A (h0end h).1
  have pB0 := fun h => hprod .B (h0end h).2
  have pA1 := fun h => hprod .A (h1end h).1
  have pB1 := fun h => hprod .B (h1end h).2
  rw [balanceA] at pA0 pA1
  rw [balanceB] at pB0 pB1
  have hall : Reaction.r0 ∈ small.reactions ∧ Reaction.r1 ∈ small.reactions := by
    by_cases h0 : Reaction.r0 ∈ small.reactions <;>
      by_cases h1 : Reaction.r1 ∈ small.reactions <;> simp_all <;> linarith
  ext r
  fin_cases r <;> simp_all [leftMotif]

private theorem right_reactions_complete
    (small : Motif network) (hsub : small.reactions ⊆ rightMotif.reactions)
    (hauto : small.IsAutocatalyticMotif) : small.reactions = rightMotif.reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have h1 : Reaction.r1 ∉ small.reactions := by
    intro h; have := hsub h; simp [rightMotif] at this
  have hne : Reaction.r0 ∈ small.reactions ∨ Reaction.r2 ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [rightMotif]
  have h0end (h0 : Reaction.r0 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hside.2.2 .r0 h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hp⟩⟩
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hp
      exact ht
  have h2end (h2 : Reaction.r2 ∈ small.reactions) :
      Species.A ∈ small.species ∧ Species.B ∈ small.species := by
    rcases hside.2.2 .r2 h2 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hp⟩⟩
    constructor
    · fin_cases t <;> norm_num [network, product] at hp
      exact ht
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
  have pA0 := fun h => hprod .A (h0end h).1
  have pB0 := fun h => hprod .B (h0end h).2
  have pA2 := fun h => hprod .A (h2end h).1
  have pB2 := fun h => hprod .B (h2end h).2
  rw [balanceA] at pA0 pA2
  rw [balanceB] at pB0 pB2
  have hall : Reaction.r0 ∈ small.reactions ∧ Reaction.r2 ∈ small.reactions := by
    by_cases h0 : Reaction.r0 ∈ small.reactions <;>
      by_cases h2 : Reaction.r2 ∈ small.reactions <;> simp_all <;> linarith
  ext r
  fin_cases r <;> simp_all [rightMotif]

private theorem species_complete (large small : Motif network)
    (hlargeSpecies : large.species = {.A, .B})
    (hreac : small.reactions = large.reactions)
    (hr0 : Reaction.r0 ∈ large.reactions) (hside : small.SideIncident) :
    small.species = large.species := by
  have h0 : Reaction.r0 ∈ small.reactions := by simpa [hreac]
  rcases hside.2.2 .r0 h0 with ⟨⟨s, hs, hsr⟩, ⟨t, ht, htp⟩⟩
  rw [hlargeSpecies]
  ext u
  fin_cases u <;> simp
  · fin_cases s <;> norm_num [network, reactant] at hsr
    exact hs
  · fin_cases t <;> norm_num [network, product] at htp
    exact ht

theorem left_isPAC : leftMotif.IsPAC := by
  constructor
  · exact ⟨left_sideIncident, commonFlow, left_productive⟩
  intro small hstrict hauto
  have hr := left_reactions_complete small hstrict.2.1 hauto
  have hs := species_complete leftMotif small rfl hr (by simp [leftMotif]) hauto.1
  rcases hstrict.2.2 with h | h
  · exact h hs
  · exact h hr

theorem right_isPAC : rightMotif.IsPAC := by
  constructor
  · exact ⟨right_sideIncident, commonFlow, right_productive⟩
  intro small hstrict hauto
  have hr := right_reactions_complete small hstrict.2.1 hauto
  have hs := species_complete rightMotif small rfl hr (by simp [rightMotif]) hauto.1
  rcases hstrict.2.2 with h | h
  · exact h hs
  · exact h hr

def family : CoreFamily (Core := Core) network where
  core | .left => leftMotif | .right => rightMotif
  core_isPAC | .left => left_isPAC | .right => right_isPAC
  orientation := fun _ => 1
  orientation_unit := by simp
  owner := fun r => if r.val = 2 then .right else .left
  owner_mem := by intro r; fin_cases r <;> simp [leftMotif, rightMotif]

theorem family_multiPAC : family.MultiPAC := by
  refine ⟨commonFlow, ?_, ?_⟩
  · intro r; fin_cases r <;> norm_num [family, commonFlow]
  · intro k; cases k with
    | left => exact left_productive
    | right => exact right_productive

noncomputable def directionPotential (s : Species) : ℝ :=
  if s = .A then -1 else -(3 / 2)

theorem family_directionCompatible : family.DirectionCompatible := by
  refine ⟨directionPotential, ?_⟩
  intro r
  fin_cases r <;> norm_num [CoreFamily.directionalAffinity,
    CoreFamily.orientedDisplacement, family, network, reactant, product,
    directionPotential, Fin.sum_univ_succ]

noncomputable def linearActivity (c : Complex Species) : ℝ :=
  match c .A, c .B with
  | 1, 0 => 4
  | 0, 1 => 3
  | 2, 0 => 9 / 4
  | 3, 0 => 11 / 4
  | _, _ => 1

theorem linearActivity_pos (c : Complex Species) : 0 < linearActivity c := by
  simp only [linearActivity]
  split <;> norm_num

theorem family_linearComplexCompatible : family.LinearComplexCompatible := by
  refine ⟨linearActivity, linearActivity_pos, ?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [family, network, ReversibleCRN.linearCurrent,
      barrier, linearActivity, reactant, product]
  · intro k
    cases k with
    | left =>
      change leftMotif.Productive (network.linearCurrent linearActivity)
      intro s hs
      fin_cases s <;> simp only [leftMotif] at hs ⊢ <;> rw [sum_left] <;>
        norm_num [network, ReversibleCRN.stoich, ReversibleCRN.linearCurrent,
          barrier, linearActivity, reactant, product]
    | right =>
      change rightMotif.Productive (network.linearCurrent linearActivity)
      intro s hs
      fin_cases s <;> simp only [rightMotif] at hs ⊢ <;> rw [sum_right] <;>
        norm_num [network, ReversibleCRN.stoich, ReversibleCRN.linearCurrent,
          barrier, linearActivity, reactant, product]

theorem no_common_species_realization
    (z : Species → ℝ)
    (hL : leftMotif.Productive (network.current z))
    (hR : rightMotif.Productive (network.current z)) : False := by
  have hLA := hL .A (by simp [leftMotif])
  have hLB := hL .B (by simp [leftMotif])
  have hRA := hR .A (by simp [rightMotif])
  have hRB := hR .B (by simp [rightMotif])
  simp only [leftMotif] at hLA hLB
  simp only [rightMotif] at hRA hRB
  rw [sum_left] at hLA hLB
  rw [sum_right] at hRA hRB
  norm_num [network, ReversibleCRN.stoich, ReversibleCRN.current,
    ReversibleCRN.complexActivity, barrier, reactant, product, Fin.prod_univ_succ]
    at hLA hLB hRA hRB
  nlinarith [sq_nonneg (z .A), mul_self_nonneg (z .A - 1)]

theorem family_not_multiCAC : ¬ family.MultiCAC := by
  rintro ⟨z, _hz, _horiented, hproductive⟩
  exact no_common_species_realization z (hproductive .left) (hproductive .right)

/-- All lower compatibility layers hold, but the toric species lift fails. -/
theorem genuineToricObstruction :
    family.MultiPAC ∧ family.DirectionCompatible ∧
      family.LinearComplexCompatible ∧ ¬ family.MultiCAC :=
  ⟨family_multiPAC, family_directionCompatible,
    family_linearComplexCompatible, family_not_multiCAC⟩

end ThermoCoreCompatibility.ToricPair

import proofs.ThermoCoreCompatibility.CoreFamily

/-!
The literal Figure 4 / Box 2 benchmark from Kosc et al.  The two cores share
`r2` and `r3`; the named external species of either core are retained in the
ambient source rather than erased.
-/

namespace ThermoCoreCompatibility.PaperPair

open scoped BigOperators
open ThermoCoreCompatibility

set_option maxHeartbeats 800000

abbrev Species := Fin 8

namespace Species
@[simp] def e1 : Species := 0
@[simp] def e2 : Species := 1
@[simp] def e3 : Species := 2
@[simp] def e4 : Species := 3
@[simp] def e1p : Species := 4
@[simp] def e2p : Species := 5
@[simp] def eA : Species := 6
@[simp] def eB : Species := 7
end Species

abbrev Reaction := Fin 6

namespace Reaction
@[simp] def r1 : Reaction := 0
@[simp] def r2 : Reaction := 1
@[simp] def r3 : Reaction := 2
@[simp] def r4 : Reaction := 3
@[simp] def r1p : Reaction := 4
@[simp] def r4p : Reaction := 5
end Reaction

inductive Core | left | right
  deriving DecidableEq, Fintype

def reactant (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 0 => 1
  | 1, 1 | 1, 5 => 1
  | 2, 2 => 1
  | 3, 6 | 3, 3 => 1
  | 4, 4 => 1
  | 5, 7 | 5, 3 => 1
  | _, _ => 0

def product (r : Reaction) (s : Species) : ℕ :=
  match r.val, s.val with
  | 0, 7 | 0, 1 => 1
  | 1, 2 => 1
  | 2, 3 => 2
  | 3, 0 => 1
  | 4, 6 | 4, 5 => 1
  | 5, 4 => 1
  | _, _ => 0

def network (barrier : Reaction → ℝ) (hbarrier : ∀ r, 0 < barrier r) :
    ReversibleCRN Species Reaction where
  reactant := reactant
  product := product
  barrier := barrier
  barrier_pos := hbarrier

variable {barrier : Reaction → ℝ} {hbarrier : ∀ r, 0 < barrier r}

def leftMotif : Motif (network barrier hbarrier) where
  species := {.e1, .e2, .e3, .e4}
  reactions := {.r1, .r2, .r3, .r4}

def rightMotif : Motif (network barrier hbarrier) where
  species := {.e1p, .e2p, .e3, .e4}
  reactions := {.r1p, .r2, .r3, .r4p}

private theorem sum_left {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r1, .r2, .r3, .r4} : Finset Reaction), f r =
      f .r1 + f .r2 + f .r3 + f .r4 := by
  simp [Finset.sum_insert, add_assoc]

private theorem sum_right {M : Type*} [AddCommMonoid M] (f : Reaction → M) :
    ∑ r ∈ ({.r1p, .r2, .r3, .r4p} : Finset Reaction), f r =
      f .r1p + f .r2 + f .r3 + f .r4p := by
  simp [Finset.sum_insert, add_assoc]

def paperFlow (r : Reaction) : ℝ :=
  match r.val with
  | 0 | 4 => 6
  | 1 => 5
  | 2 => 4
  | _ => 7

theorem left_sideIncident : (leftMotif (barrier := barrier) (hbarrier := hbarrier)).SideIncident := by
  constructor
  · exact ⟨.e1, by simp [leftMotif]⟩
  constructor
  · exact ⟨.r1, by simp [leftMotif]⟩
  intro r hr
  fin_cases r <;> simp_all [leftMotif, network, reactant, product]

theorem right_sideIncident : (rightMotif (barrier := barrier) (hbarrier := hbarrier)).SideIncident := by
  constructor
  · exact ⟨.e1p, by simp [rightMotif]⟩
  constructor
  · exact ⟨.r1p, by simp [rightMotif]⟩
  intro r hr
  fin_cases r <;> simp_all [rightMotif, network, reactant, product]

theorem left_productive :
    (leftMotif (barrier := barrier) (hbarrier := hbarrier)).Productive paperFlow := by
  intro s hs
  fin_cases s
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [leftMotif]; rw [sum_left]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs

theorem right_productive :
    (rightMotif (barrier := barrier) (hbarrier := hbarrier)).Productive paperFlow := by
  intro s hs
  fin_cases s
  · simp [rightMotif] at hs
  · simp [rightMotif] at hs
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp only [rightMotif]; rw [sum_right]; norm_num [network, ReversibleCRN.stoich, reactant, product, paperFlow]
  · simp [rightMotif] at hs
  · simp [rightMotif] at hs

theorem paperPair_exact_flow_preflight :
    (leftMotif (barrier := barrier) (hbarrier := hbarrier)).Productive paperFlow ∧
    (rightMotif (barrier := barrier) (hbarrier := hbarrier)).Productive paperFlow :=
  ⟨left_productive, right_productive⟩

private theorem sum_over_reactions (S : Finset Reaction) (f : Reaction → ℝ) :
    ∑ r ∈ S, f r = ∑ r : Reaction, (if r ∈ S then f r else 0) := by
  calc
    ∑ r ∈ S, f r = ∑ r ∈ S, (if r ∈ S then f r else 0) := by simp
    _ = ∑ r ∈ Finset.univ, (if r ∈ S then f r else 0) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro r _ hr
      simp [hr]

private theorem enum_r4 : (Fin.succ (2 : Fin 5) : Reaction) = Reaction.r4 := by decide

private theorem enum_r1p : (Fin.succ (Fin.succ (2 : Fin 4)) : Reaction) = Reaction.r1p := by
  decide

private theorem enum_r4p :
    (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3))) : Reaction) = Reaction.r4p := by
  decide

private theorem left_balance_e1 (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e1 r : ℝ) * v r =
      (if .r1 ∈ S then -v .r1 else 0) + (if .r4 ∈ S then v .r4 else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e1 r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]
      simp [enum_r4]

private theorem left_balance_e2 (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e2 r : ℝ) * v r =
      (if .r1 ∈ S then v .r1 else 0) + (if .r2 ∈ S then -v .r2 else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e2 r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]

private theorem left_balance_e3 (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e3 r : ℝ) * v r =
      (if .r2 ∈ S then v .r2 else 0) + (if .r3 ∈ S then -v .r3 else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e3 r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]

private theorem left_balance_e4 (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e4 r : ℝ) * v r =
      (if .r3 ∈ S then 2 * v .r3 else 0) + (if .r4 ∈ S then -v .r4 else 0) +
        (if .r4p ∈ S then -v .r4p else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e4 r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]
      simp [enum_r4, add_assoc]

theorem cycle_support_complete
    (m0 m1 m2 m3 : Prop) [Decidable m0] [Decidable m1] [Decidable m2] [Decidable m3]
    (v0 v1 v2 v3 : ℝ) (hne : m0 ∨ m1 ∨ m2 ∨ m3)
    (p0a : m0 → 0 < (if m0 then -v0 else 0) + (if m3 then v3 else 0))
    (p0b : m0 → 0 < (if m0 then v0 else 0) + (if m1 then -v1 else 0))
    (p1a : m1 → 0 < (if m0 then v0 else 0) + (if m1 then -v1 else 0))
    (p1b : m1 → 0 < (if m1 then v1 else 0) + (if m2 then -v2 else 0))
    (p2a : m2 → 0 < (if m1 then v1 else 0) + (if m2 then -v2 else 0))
    (p2b : m2 → 0 < (if m2 then 2 * v2 else 0) + (if m3 then -v3 else 0))
    (p3a : m3 → 0 < (if m2 then 2 * v2 else 0) + (if m3 then -v3 else 0))
    (p3b : m3 → 0 < (if m0 then -v0 else 0) + (if m3 then v3 else 0)) :
    m0 ∧ m1 ∧ m2 ∧ m3 := by
  by_cases h0 : m0 <;> by_cases h1 : m1 <;> by_cases h2 : m2 <;> by_cases h3 : m3 <;>
    simp_all <;> linarith

private theorem left_reactions_complete
    (small : Motif (network barrier hbarrier))
    (hsp : small.species ⊆ (leftMotif (barrier := barrier) (hbarrier := hbarrier)).species)
    (hsub : small.reactions ⊆ (leftMotif (barrier := barrier) (hbarrier := hbarrier)).reactions)
    (hauto : small.IsAutocatalyticMotif) :
    small.reactions = (leftMotif (barrier := barrier) (hbarrier := hbarrier)).reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have hp := hside.2.2
  have h0end (h0 : Reaction.r1 ∈ small.reactions) :
      Species.e1 ∈ small.species ∧ Species.e2 ∈ small.species := by
    rcases hp .r1 h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have ht' := hsp ht
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      · exact ht
      · simp [leftMotif] at ht'
  have h1end (h1 : Reaction.r2 ∈ small.reactions) :
      Species.e2 ∈ small.species ∧ Species.e3 ∈ small.species := by
    rcases hp .r2 h1 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have hs' := hsp hs
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      · exact hs
      · simp [leftMotif] at hs'
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h2end (h2 : Reaction.r3 ∈ small.reactions) :
      Species.e3 ∈ small.species ∧ Species.e4 ∈ small.species := by
    rcases hp .r3 h2 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h3end (h3 : Reaction.r4 ∈ small.reactions) :
      Species.e4 ∈ small.species ∧ Species.e1 ∈ small.species := by
    rcases hp .r4 h3 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have hs' := hsp hs
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      · exact hs
      · simp [leftMotif] at hs'
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h4 : Reaction.r1p ∉ small.reactions := by
    intro h
    have := hsub h
    simp [leftMotif] at this
  have h5 : Reaction.r4p ∉ small.reactions := by
    intro h
    have := hsub h
    simp [leftMotif] at this
  have hne : Reaction.r1 ∈ small.reactions ∨ Reaction.r2 ∈ small.reactions ∨
      Reaction.r3 ∈ small.reactions ∨ Reaction.r4 ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [leftMotif]
  have p0a := fun h => hprod .e1 (h0end h).1
  have p0b := fun h => hprod .e2 (h0end h).2
  have p1a := fun h => hprod .e2 (h1end h).1
  have p1b := fun h => hprod .e3 (h1end h).2
  have p2a := fun h => hprod .e3 (h2end h).1
  have p2b := fun h => hprod .e4 (h2end h).2
  have p3a := fun h => hprod .e4 (h3end h).1
  have p3b := fun h => hprod .e1 (h3end h).2
  rw [left_balance_e1] at p0a p3b
  rw [left_balance_e2] at p0b p1a
  rw [left_balance_e3] at p1b p2a
  rw [left_balance_e4] at p2b p3a
  have h5num : (5 : Reaction) ∉ small.reactions := by
    simpa [Reaction.r4p] using h5
  have p2b' : Reaction.r3 ∈ small.reactions →
      0 < (if Reaction.r3 ∈ small.reactions then 2 * v .r3 else 0) +
        (if Reaction.r4 ∈ small.reactions then -v .r4 else 0) := by
    intro h
    simpa [h5num] using p2b h
  have p3a' : Reaction.r4 ∈ small.reactions →
      0 < (if Reaction.r3 ∈ small.reactions then 2 * v .r3 else 0) +
        (if Reaction.r4 ∈ small.reactions then -v .r4 else 0) := by
    intro h
    simpa [h5num] using p3a h
  have hall := cycle_support_complete
    (Reaction.r1 ∈ small.reactions) (Reaction.r2 ∈ small.reactions)
    (Reaction.r3 ∈ small.reactions) (Reaction.r4 ∈ small.reactions)
    (v .r1) (v .r2) (v .r3) (v .r4) hne p0a p0b p1a p1b p2a p2b' p3a' p3b
  ext r
  fin_cases r <;> simp_all [leftMotif]

private theorem left_species_complete
    (small : Motif (network barrier hbarrier))
    (hsp : small.species ⊆ (leftMotif (barrier := barrier) (hbarrier := hbarrier)).species)
    (hreac : small.reactions = (leftMotif (barrier := barrier) (hbarrier := hbarrier)).reactions)
    (hside : small.SideIncident) :
    small.species = (leftMotif (barrier := barrier) (hbarrier := hbarrier)).species := by
  apply Finset.Subset.antisymm hsp
  intro s hs
  fin_cases s
  · rcases (hside.2.2 .r1 (by rw [hreac]; simp [leftMotif])).1 with ⟨t, ht, hreact⟩
    fin_cases t <;> norm_num [network, reactant] at hreact
    exact ht
  · rcases (hside.2.2 .r1 (by rw [hreac]; simp [leftMotif])).2 with ⟨t, ht, hprod⟩
    have ht' := hsp ht
    fin_cases t <;> norm_num [network, product] at hprod
    · exact ht
    · simp [leftMotif] at ht'
  · rcases (hside.2.2 .r2 (by rw [hreac]; simp [leftMotif])).2 with ⟨t, ht, hprod⟩
    fin_cases t <;> norm_num [network, product] at hprod
    exact ht
  · rcases (hside.2.2 .r3 (by rw [hreac]; simp [leftMotif])).2 with ⟨t, ht, hprod⟩
    fin_cases t <;> norm_num [network, product] at hprod
    exact ht
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs
  · simp [leftMotif] at hs

theorem left_isPAC :
    (leftMotif (barrier := barrier) (hbarrier := hbarrier)).IsPAC := by
  constructor
  · exact ⟨left_sideIncident, paperFlow, left_productive⟩
  intro small hstrict hauto
  have hreac := left_reactions_complete small hstrict.1 hstrict.2.1 hauto
  have hspecies := left_species_complete small hstrict.1 hreac hauto.1
  rcases hstrict.2.2 with hs | hr
  · exact hs hspecies
  · exact hr hreac

private theorem right_balance_e1p (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e1p r : ℝ) * v r =
      (if .r1p ∈ S then -v .r1p else 0) + (if .r4p ∈ S then v .r4p else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e1p r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]
      simp

private theorem right_balance_e2p (S : Finset Reaction) (v : Reaction → ℝ) :
    ∑ r ∈ S, ((network barrier hbarrier).stoich .e2p r : ℝ) * v r =
      (if .r1p ∈ S then v .r1p else 0) + (if .r2 ∈ S then -v .r2 else 0) := by
  calc
    _ = ∑ r : Reaction, (if r ∈ S then
        ((network barrier hbarrier).stoich .e2p r : ℝ) * v r else 0) :=
      sum_over_reactions S _
    _ = _ := by
      simp only [Fin.sum_univ_succ]
      norm_num [network, ReversibleCRN.stoich, reactant, product]
      simp [add_comm]

private theorem right_reactions_complete
    (small : Motif (network barrier hbarrier))
    (hsp : small.species ⊆ (rightMotif (barrier := barrier) (hbarrier := hbarrier)).species)
    (hsub : small.reactions ⊆ (rightMotif (barrier := barrier) (hbarrier := hbarrier)).reactions)
    (hauto : small.IsAutocatalyticMotif) :
    small.reactions = (rightMotif (barrier := barrier) (hbarrier := hbarrier)).reactions := by
  rcases hauto with ⟨hside, v, hprod⟩
  have hp := hside.2.2
  have h0end (h0 : Reaction.r1p ∈ small.reactions) :
      Species.e1p ∈ small.species ∧ Species.e2p ∈ small.species := by
    rcases hp .r1p h0 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have ht' := hsp ht
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      · exact ht
      · simp [rightMotif] at ht'
  have h1end (h1 : Reaction.r2 ∈ small.reactions) :
      Species.e2p ∈ small.species ∧ Species.e3 ∈ small.species := by
    rcases hp .r2 h1 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have hs' := hsp hs
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      · simp [rightMotif] at hs'
      · exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h2end (h2 : Reaction.r3 ∈ small.reactions) :
      Species.e3 ∈ small.species ∧ Species.e4 ∈ small.species := by
    rcases hp .r3 h2 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      exact hs
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have h3end (h3 : Reaction.r4p ∈ small.reactions) :
      Species.e4 ∈ small.species ∧ Species.e1p ∈ small.species := by
    rcases hp .r4p h3 with ⟨⟨s, hs, hr⟩, ⟨t, ht, hq⟩⟩
    have hs' := hsp hs
    clear hprod hside hp v
    constructor
    · fin_cases s <;> norm_num [network, reactant] at hr
      · exact hs
      · simp [rightMotif] at hs'
    · fin_cases t <;> norm_num [network, product] at hq
      exact ht
  have hleft1 : Reaction.r1 ∉ small.reactions := by
    intro h; have := hsub h; simp [rightMotif] at this
  have hleft4 : Reaction.r4 ∉ small.reactions := by
    intro h; have := hsub h; simp [rightMotif] at this
  have hne : Reaction.r1p ∈ small.reactions ∨ Reaction.r2 ∈ small.reactions ∨
      Reaction.r3 ∈ small.reactions ∨ Reaction.r4p ∈ small.reactions := by
    rcases hside.2.1 with ⟨r, hr⟩
    fin_cases r <;> simp_all [rightMotif]
  have p0a := fun h => hprod .e1p (h0end h).1
  have p0b := fun h => hprod .e2p (h0end h).2
  have p1a := fun h => hprod .e2p (h1end h).1
  have p1b := fun h => hprod .e3 (h1end h).2
  have p2a := fun h => hprod .e3 (h2end h).1
  have p2b := fun h => hprod .e4 (h2end h).2
  have p3a := fun h => hprod .e4 (h3end h).1
  have p3b := fun h => hprod .e1p (h3end h).2
  rw [right_balance_e1p] at p0a p3b
  rw [right_balance_e2p] at p0b p1a
  rw [left_balance_e3] at p1b p2a
  rw [left_balance_e4] at p2b p3a
  have hleft4num : (3 : Reaction) ∉ small.reactions := by
    simpa [Reaction.r4] using hleft4
  have p2b' : Reaction.r3 ∈ small.reactions →
      0 < (if Reaction.r3 ∈ small.reactions then 2 * v .r3 else 0) +
        (if Reaction.r4p ∈ small.reactions then -v .r4p else 0) := by
    intro h
    simpa [hleft4num, add_assoc] using p2b h
  have p3a' : Reaction.r4p ∈ small.reactions →
      0 < (if Reaction.r3 ∈ small.reactions then 2 * v .r3 else 0) +
        (if Reaction.r4p ∈ small.reactions then -v .r4p else 0) := by
    intro h
    simpa [hleft4num, add_assoc] using p3a h
  have hall := cycle_support_complete
    (Reaction.r1p ∈ small.reactions) (Reaction.r2 ∈ small.reactions)
    (Reaction.r3 ∈ small.reactions) (Reaction.r4p ∈ small.reactions)
    (v .r1p) (v .r2) (v .r3) (v .r4p) hne p0a p0b p1a p1b p2a p2b' p3a' p3b
  ext r
  fin_cases r <;> simp_all [rightMotif]

private theorem right_species_complete
    (small : Motif (network barrier hbarrier))
    (hsp : small.species ⊆ (rightMotif (barrier := barrier) (hbarrier := hbarrier)).species)
    (hreac : small.reactions = (rightMotif (barrier := barrier) (hbarrier := hbarrier)).reactions)
    (hside : small.SideIncident) :
    small.species = (rightMotif (barrier := barrier) (hbarrier := hbarrier)).species := by
  apply Finset.Subset.antisymm hsp
  intro s hs
  fin_cases s
  · simp [rightMotif] at hs
  · simp [rightMotif] at hs
  · rcases (hside.2.2 .r2 (by rw [hreac]; simp [rightMotif])).2 with ⟨t, ht, hprod⟩
    fin_cases t <;> norm_num [network, product] at hprod
    exact ht
  · rcases (hside.2.2 .r3 (by rw [hreac]; simp [rightMotif])).2 with ⟨t, ht, hprod⟩
    fin_cases t <;> norm_num [network, product] at hprod
    exact ht
  · rcases (hside.2.2 .r1p (by rw [hreac]; simp [rightMotif])).1 with ⟨t, ht, hreact⟩
    fin_cases t <;> norm_num [network, reactant] at hreact
    exact ht
  · rcases (hside.2.2 .r1p (by rw [hreac]; simp [rightMotif])).2 with ⟨t, ht, hprod⟩
    have ht' := hsp ht
    fin_cases t <;> norm_num [network, product] at hprod
    · exact ht
    · simp [rightMotif] at ht'
  · simp [rightMotif] at hs
  · simp [rightMotif] at hs

theorem right_isPAC :
    (rightMotif (barrier := barrier) (hbarrier := hbarrier)).IsPAC := by
  constructor
  · exact ⟨right_sideIncident, paperFlow, right_productive⟩
  intro small hstrict hauto
  have hreac := right_reactions_complete small hstrict.1 hstrict.2.1 hauto
  have hspecies := right_species_complete small hstrict.1 hreac hauto.1
  rcases hstrict.2.2 with hs | hr
  · exact hs hspecies
  · exact hr hreac

def paperFamily : CoreFamily (Core := Core) (network barrier hbarrier) where
  core
    | .left => leftMotif
    | .right => rightMotif
  core_isPAC
    | .left => left_isPAC
    | .right => right_isPAC
  orientation := fun _ => 1
  orientation_unit := by intro r; exact Or.inl rfl
  owner := fun r => if r = .r1p ∨ r = .r4p then .right else .left
  owner_mem := by
    intro r
    fin_cases r <;> simp [leftMotif, rightMotif]

theorem paperFamily_multiPAC :
    (paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiPAC := by
  refine ⟨paperFlow, ?_, ?_⟩
  · intro r
    fin_cases r <;> norm_num [paperFamily, paperFlow]
  intro k
  cases k
  · exact left_productive
  · exact right_productive

private theorem currents_positive_of_both_productive
    {v : Reaction → ℝ}
    (hL : (leftMotif (barrier := barrier) (hbarrier := hbarrier)).Productive v)
    (hR : (rightMotif (barrier := barrier) (hbarrier := hbarrier)).Productive v) :
    (∀ r, 0 < v r) := by
  have h1 := hL .e1 (by simp [leftMotif])
  have h2 := hL .e2 (by simp [leftMotif])
  have h3 := hL .e3 (by simp [leftMotif])
  have h4 := hL .e4 (by simp [leftMotif])
  have h1p := hR .e1p (by simp [rightMotif])
  have h2p := hR .e2p (by simp [rightMotif])
  have h3p := hR .e3 (by simp [rightMotif])
  have h4p := hR .e4 (by simp [rightMotif])
  simp only [leftMotif] at h1 h2 h3 h4
  simp only [rightMotif] at h1p h2p h3p h4p
  rw [sum_left] at h1 h2 h3 h4
  rw [sum_right] at h1p h2p h3p h4p
  norm_num [network, ReversibleCRN.stoich, reactant, product] at h1 h2 h3 h4 h1p h2p h3p h4p
  have hv3 : 0 < v (2 : Reaction) := by linarith
  have hv2 : 0 < v (1 : Reaction) := by linarith
  have hv1 : 0 < v (0 : Reaction) := by linarith
  have hv4 : 0 < v (3 : Reaction) := by linarith
  have hv1p : 0 < v (4 : Reaction) := by linarith
  have hv4p : 0 < v (5 : Reaction) := by linarith
  intro r
  fin_cases r
  · simpa using hv1
  · simpa using hv2
  · simpa using hv3
  · simpa using hv4
  · simpa using hv1p
  · simpa using hv4p

private theorem current_pos_iff_monomial_lt
    (z : Species → ℝ) (r : Reaction) :
    0 < (network barrier hbarrier).current z r ↔
      ReversibleCRN.complexActivity z (product r) <
        ReversibleCRN.complexActivity z (reactant r) := by
  simp only [ReversibleCRN.current, network]
  rw [mul_pos_iff_of_pos_left (hbarrier r), sub_pos]

theorem no_common_thermodynamic_witness
    (z : Species → ℝ) (hz : ∀ s, 0 < z s)
    (hL : (leftMotif (barrier := barrier) (hbarrier := hbarrier)).Productive
      ((network barrier hbarrier).current z))
    (hR : (rightMotif (barrier := barrier) (hbarrier := hbarrier)).Productive
      ((network barrier hbarrier).current z)) : False := by
  have hp := currents_positive_of_both_productive hL hR
  have hr1 := (current_pos_iff_monomial_lt z .r1).1 (hp .r1)
  have hr2 := (current_pos_iff_monomial_lt z .r2).1 (hp .r2)
  have hr3 := (current_pos_iff_monomial_lt z .r3).1 (hp .r3)
  have hr4 := (current_pos_iff_monomial_lt z .r4).1 (hp .r4)
  have hr1p := (current_pos_iff_monomial_lt z .r1p).1 (hp .r1p)
  have hr4p := (current_pos_iff_monomial_lt z .r4p).1 (hp .r4p)
  simp [ReversibleCRN.complexActivity, reactant, product, Fin.prod_univ_succ] at hr1 hr2 hr3 hr4 hr1p hr4p
  have hfirst : z .eB * z .e2 < z .eA * z .e4 := by
    simpa [mul_comm] using lt_trans hr1 hr4
  have hsecond : z .eA * z .e2p < z .eB * z .e4 := by
    simpa [mul_comm] using lt_trans hr1p hr4p
  have htoric : z .e4 ^ 2 < z .e2 * z .e2p := by
    simpa [mul_comm] using lt_trans hr3 hr2
  have hmult :
      (z .eB * z .e2) * (z .eA * z .e2p) <
        (z .eA * z .e4) * (z .eB * z .e4) :=
    mul_lt_mul hfirst (le_of_lt hsecond) (mul_pos (hz .eA) (hz .e2p))
      (le_of_lt (mul_pos (hz .eA) (hz .e4)))
  have hscaled := mul_lt_mul_of_pos_left htoric (mul_pos (hz .eA) (hz .eB))
  nlinarith

theorem paperFamily_not_multiCAC :
    ¬ (paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiCAC := by
  rintro ⟨z, hz, _horiented, hproductive⟩
  exact no_common_thermodynamic_witness z hz
    (hproductive .left) (hproductive .right)

theorem paperPair_multiPAC_not_multiCAC :
    (paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiPAC ∧
      ¬ (paperFamily (barrier := barrier) (hbarrier := hbarrier)).MultiCAC :=
  ⟨paperFamily_multiPAC, paperFamily_not_multiCAC⟩

end ThermoCoreCompatibility.PaperPair

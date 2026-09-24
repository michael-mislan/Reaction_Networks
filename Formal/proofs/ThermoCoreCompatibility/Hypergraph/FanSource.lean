import proofs.ThermoCoreCompatibility.Hypergraph.TriangleSource
import proofs.ThermoCoreCompatibility.Hypergraph.FanUnivariate

namespace ThermoCoreCompatibility.Hypergraph

abbrev FanSpecies (ι : Type*) := Option (Option ι)
abbrev FanReaction (ι : Type*) := Option (ι × Bool)

def FanData.network {ι : Type*} [DecidableEq ι] (D : FanData ι) :
    ReversibleCRN (FanSpecies ι) (FanReaction ι) where
  reactant
    | none => atom none 1
    | some (_,false) => atom (some none) 1
    | some (i,true) => atom (some (some i)) 1
  product
    | none => atom (some none) 1
    | some (i,false) => atom (some (some i)) 1
    | some (i,true) => atom none (D.gain i)
  barrier
    | none => D.sharedFactor
    | some (i,false) => D.firstFactor i
    | some (i,true) => D.secondFactor i
  barrier_pos := by
    intro r
    rcases r with _ | ⟨i,(_|_)⟩
    · exact D.sharedFactor_pos
    · exact D.firstFactor_pos i
    · exact D.secondFactor_pos i

def FanData.triangle {ι : Type*} [DecidableEq ι] (D : FanData ι) (i : ι) :
    TriangleIn D.network where
  A := none
  B := some none
  C := some (some i)
  AB := by simp
  AC := by simp
  BC := by simp
  r₀ := none
  r₁ := some (i,false)
  r₂ := some (i,true)
  r01 := by simp
  r02 := by simp
  r12 := by simp
  gain := D.gain i
  gain_ge_two := D.gain_ge_two i
  react₀ := rfl
  prod₀ := rfl
  react₁ := rfl
  prod₁ := rfl
  react₂ := rfl
  prod₂ := rfl

theorem FanData.source_isPAC {ι : Type*} [DecidableEq ι] (D : FanData ι) (i : ι) :
    (D.triangle i).motif.IsPAC := (D.triangle i).isPAC

theorem triangle_currents_positive {m j₀ j₁ j₂ : ℝ} (hm : 1 ≤ m)
    (h₀ : j₀ < m*j₂) (h₁ : j₁ < j₀) (h₂ : j₂ < j₁) :
    0 < j₀ ∧ 0 < j₁ ∧ 0 < j₂ := by
  have hp : 0 < j₂ := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hm) (le_of_not_gt hn)
    nlinarith
  exact ⟨lt_trans (lt_trans hp h₂) h₁,lt_trans hp h₂,hp⟩

/-- Source predicate for retained motifs. Deletion does not preserve the
omitted motif's orientation requirements, and does not change any box. -/
def FanData.SourceCompatible {ι : Type*} [DecidableEq ι] [Fintype ι]
    (D : FanData ι) (F : Set ι) (la ua lb ub : ℝ) : Prop :=
  ∃ z : FanSpecies ι → ℝ,
    (∀ s, 0 < z s) ∧
    la ≤ z none ∧ z none ≤ ua ∧ lb ≤ z (some none) ∧ z (some none) ≤ ub ∧
    (∀ i, D.lower i ≤ z (some (some i)) ∧ z (some (some i)) ≤ D.upper i) ∧
    ∀ i ∈ F, (D.triangle i).motif.Productive (D.network.current z) ∧
      ∀ r ∈ (D.triangle i).motif.reactions, 0 < D.network.current z r

end ThermoCoreCompatibility.Hypergraph

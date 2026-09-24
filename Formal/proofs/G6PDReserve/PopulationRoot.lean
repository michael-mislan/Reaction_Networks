import proofs.G6PDReserve.WeightedPopulation
import proofs.G6PDReserve.ReadoutBounds

namespace G6PDReserve.Population
noncomputable section
open Set
open scoped BigOperators

/-- The derivative is the literal source law, with the declared clamped inputs. -/
def LiteralSolution (V : ℝ) (g : ℝ → ℝ) : Prop :=
  g 0 = 10 ∧ (∀ t ∈ Icc 0 120, g t ∈ Icc 0 56) ∧
    ∀ t ∈ Icc 0 120, HasDerivAt g
      (shimoRate V 3 7 56 125 520 (56-g t) 7 (g t) 0 0-3/10) t

theorem literal_solution_iff (V : ℝ) (g : ℝ → ℝ) : LiteralSolution V g ↔ Solution V g := by
  simp only [LiteralSolution, Solution, literal_rate]

/-- Every admitted population has actual source solutions; all such solutions
have the same classified fraction and satisfy both observation bounds. -/
theorem population_guarantee {ι : Type*} [Fintype ι] (P : Pop ι) :
    (∃ g : ι → ℝ → ℝ, ∀ i, LiteralSolution (P.V i) (g i)) ∧
    (∀ N S H A B : ℝ,
      (∑ i, P.w i * shimoRate (P.V i) 3 7 56 125 520 N S H A B) =
        shimoRate 1 3 7 56 125 520 N S H A B) ∧
    (∀ g : ι → ℝ → ℝ, (∀ i, LiteralSolution (P.V i) (g i)) →
      (20/41 ≤ actualFraction P g ∧ actualFraction P g ≤ 1) ∧
      (∀ s f r, Readout (actualFraction P g) s f r →
        33/49 ≤ actualFraction P g ∧ actualFraction P g ≤ 4/5)) := by
  obtain ⟨g,hg⟩ := all_solutions P
  refine ⟨⟨g,fun i => (literal_solution_iff _ _).mpr (hg i)⟩,bulk_surface P,?_⟩
  intro g hg
  have he := actual_eq P g (fun i => (literal_solution_iff _ _).mp (hg i))
  rw [he]
  have hb := fraction_bounds P
  exact ⟨hb,fun _ _ _ hr => readout_bounds (by linarith [hb.1]) hb.2 hr⟩

def Realized (p : ℝ) : Prop := ∃ P : Pop (Fin 3), ∃ g : Fin 3 → ℝ → ℝ,
  (∀ i, LiteralSolution (P.V i) (g i)) ∧ actualFraction P g = p

def RepairedRealized (p : ℝ) : Prop := ∃ P : Pop (Fin 3), ∃ g : Fin 3 → ℝ → ℝ,
  (∀ i, LiteralSolution (P.V i) (g i)) ∧ actualFraction P g = p ∧
  ∃ s f r, Readout (actualFraction P g) s f r

/-- Constructive sharpness: every point, including both endpoints, is attained. -/
theorem sharp_bulk (p : ℝ) : Realized p ↔ 20/41 ≤ p ∧ p ≤ 1 := by
  constructor
  · rintro ⟨P,g,hg,rfl⟩
    exact ((population_guarantee P).2.2 g hg).1
  · rintro ⟨hl,hu⟩
    let P := witness p hl hu
    obtain ⟨g,hg⟩ := (population_guarantee P).1
    refine ⟨P,g,hg,?_⟩
    rw [actual_eq P g (fun i => (literal_solution_iff _ _).mp (hg i))]
    exact witness_fraction p hl hu

/-- The repair is sharp in the same kinetic and mean-constrained class. -/
theorem sharp_repaired (p : ℝ) : RepairedRealized p ↔ 33/49 ≤ p ∧ p ≤ 4/5 := by
  constructor
  · rintro ⟨P,g,hg,rfl,s,f,r,hr⟩
    exact ((population_guarantee P).2.2 g hg).2 s f r hr
  · rintro ⟨hl,hu⟩
    obtain ⟨P,g,hg,he⟩ := (sharp_bulk p).mpr ⟨by linarith,by linarith⟩
    refine ⟨P,g,hg,he,?_⟩
    rw [he]
    exact readout_feasible p hl hu

/-- Source-specific population root, including universal validity, nonempty
literal dynamics, whole bulk response equivalence, and both exact identified sets.
Readout calibration is explicitly conditional; no clinical claim is asserted. -/
theorem population_root :
    (∀ n : ℕ, ∀ P : Pop (Fin n),
      (∃ g : Fin n → ℝ → ℝ, ∀ i, LiteralSolution (P.V i) (g i)) ∧
      (∀ N S H A B : ℝ,
        (∑ i, P.w i * shimoRate (P.V i) 3 7 56 125 520 N S H A B) =
          shimoRate 1 3 7 56 125 520 N S H A B) ∧
      (∀ g : Fin n → ℝ → ℝ, (∀ i, LiteralSolution (P.V i) (g i)) →
        (20/41 ≤ actualFraction P g ∧ actualFraction P g ≤ 1) ∧
        (∀ s f r, Readout (actualFraction P g) s f r →
          33/49 ≤ actualFraction P g ∧ actualFraction P g ≤ 4/5))) ∧
    (∀ p : ℝ, Realized p ↔ 20/41 ≤ p ∧ p ≤ 1) ∧
    (∀ p : ℝ, RepairedRealized p ↔ 33/49 ≤ p ∧ p ≤ 4/5) := by
  exact ⟨fun _ P => population_guarantee P, sharp_bulk, sharp_repaired⟩

end
end G6PDReserve.Population

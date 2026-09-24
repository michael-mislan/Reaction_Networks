import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace InheritedCellAssay
open scoped BigOperators

/-- A founder configuration is the subset of independently fair founders in state H.
Every subset has weight 2^(-F). No descendant is an independent draw. -/
def sourceExpectation (F : ℕ) (f : Finset (Fin F) → ℚ) : ℚ :=
  (∑ s ∈ (Finset.univ : Finset (Fin F)).powerset, f s) / 2^F

/-- Compressed observation law, to be connected to the subset source below. -/
def countExpectation (F : ℕ) (f : ℕ → ℚ) : ℚ :=
  (∑ h ∈ Finset.range (F+1), (F.choose h : ℚ) * f h) / 2^F

/-- Structural compression, valid for every founder count and every observable.
This counts configurations by their number of H founders; it is not enumeration. -/
theorem source_count_transport (F : ℕ) (f : ℕ → ℚ) :
    sourceExpectation F (fun s => f s.card) = countExpectation F f := by
  unfold sourceExpectation countExpectation
  rw [Finset.sum_powerset]
  simp_rw [Finset.sum_powersetCard]
  simp [nsmul_eq_mul]

theorem source_normalized (F : ℕ) : sourceExpectation F (fun _ => 1) = 1 := by
  simp [sourceExpectation]

/-- Complete deterministic offspring list; false is a continuation, true a division. -/
def offspring (b : Bool) : List Bool := if b then [true, true] else [false]

def descendants : ℕ → Bool → List Bool
  | 0, b => [b]
  | g+1, b => (offspring b).flatMap (descendants g)

theorem high_descendants (g : ℕ) : descendants g true = List.replicate (2^g) true := by
  induction g with
  | zero => simp [descendants]
  | succ g ih =>
    simp [descendants, offspring, ih, pow_succ, Nat.mul_two]

theorem low_descendants (g : ℕ) : descendants g false = [false] := by
  induction g with
  | zero => rfl
  | succ g ih => simp [descendants, offspring, ih]

/-- All cells at the endpoint, with a block for every H and every L founder. -/
noncomputable def endpoint (F g : ℕ) (s : Finset (Fin F)) : List Bool :=
  s.toList.flatMap (fun _ => descendants g true) ++
  ((Finset.univ : Finset (Fin F)) \ s).toList.flatMap (fun _ => descendants g false)

theorem endpoint_count (F g : ℕ) (s : Finset (Fin F)) :
    (endpoint F g s).length = 2^g*s.card + (F-s.card) := by
  simp [endpoint, high_descendants, low_descendants, List.length_flatMap,
    Finset.card_sdiff, Nat.mul_comm]

theorem endpoint_response (F g : ℕ) (s : Finset (Fin F)) :
    ((endpoint F g s).filter id).length = 2^g*s.card := by
  simp [endpoint, high_descendants, low_descendants, List.filter_flatMap,
    List.length_flatMap, Nat.mul_comm]

def scoreAccept (n r : ℚ) (p : ℚ) : Prop :=
  (r/n-p)^2 ≤ (49/25 : ℚ)^2*p*(1-p)/n

instance (n r p : ℚ) : Decidable (scoreAccept n r p) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Four perfect binary divisions: each H founder supplies sixteen H leaves. -/
def perfectCopyCoverage : ℚ :=
  countExpectation 10 (fun h => if scoreAccept 160 (16*h) (1/2) then 1 else 0)

theorem perfect_copy_score_coverage : perfectCopyCoverage = 63/256 := by
  norm_num [perfectCopyCoverage, countExpectation, scoreAccept,
    Finset.sum_range_succ, Nat.choose]

/-- Three generations of H -> [H,H] and L -> [L]. All endpoints are observed. -/
def selectiveFraction (F h : ℕ) : ℚ := (8*h : ℚ) / (8*h+(F-h : ℕ))

def selectiveFailure (F : ℕ) : ℚ :=
  countExpectation F (fun h => if |selectiveFraction F h-8/9| > 1/10 then 1 else 0)

theorem selective_twenty_insufficient : selectiveFailure 20 > 1/20 := by
  norm_num [selectiveFailure, countExpectation, selectiveFraction,
    Finset.sum_range_succ, Nat.choose, abs_of_nonneg, abs_of_neg]

theorem selective_thirty_sufficient : selectiveFailure 30 < 1/20 := by
  norm_num [selectiveFailure, countExpectation, selectiveFraction,
    Finset.sum_range_succ, Nat.choose, abs_of_nonneg, abs_of_neg]

/-- Actual endpoint readout; no substitute deterministic denominator is used. -/
noncomputable def readout (F : ℕ) (s : Finset (Fin F)) : ℚ :=
  (((endpoint F 3 s).filter id).length : ℚ) / (endpoint F 3 s).length

theorem readout_eq (F : ℕ) (s : Finset (Fin F)) :
    readout F s = selectiveFraction F s.card := by
  simp [readout, endpoint_count, endpoint_response, selectiveFraction]

noncomputable def actualFailure (F : ℕ) : ℚ :=
  sourceExpectation F (fun s => if |readout F s - 8/9| > 1/10 then 1 else 0)

theorem actual_failure_transport (F : ℕ) : actualFailure F = selectiveFailure F := by
  simp_rw [actualFailure, readout_eq]
  exact source_count_transport F (fun h =>
    if |selectiveFraction F h - 8/9| > 1/10 then 1 else 0)

theorem endpoint_nonempty (F : ℕ) (hF : 0 < F) (s : Finset (Fin F)) :
    0 < (endpoint F 3 s).length := by
  rw [endpoint_count]
  have hcard : s.card ≤ F := by
    simpa using Finset.card_le_univ s
  norm_num only [Nat.reducePow]
  omega

/-- Finite source-connected design decision. This is an explicitly synthetic theorem. -/
theorem resolution :
    actualFailure 20 > 1/20 ∧ actualFailure 30 < 1/20 ∧
    (∀ s : Finset (Fin 30), 0 < (endpoint 30 3 s).length) := by
  rw [actual_failure_transport, actual_failure_transport]
  exact ⟨selective_twenty_insufficient, selective_thirty_sufficient,
    endpoint_nonempty 30 (by norm_num)⟩

end InheritedCellAssay

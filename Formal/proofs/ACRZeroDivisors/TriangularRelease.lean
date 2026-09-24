import proofs.ACRZeroDivisors.GraphIdeal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.LinearCombination

namespace ACRZeroDivisors
open MvPolynomial

def triangularDifferences {A : Type*} [CommRing A] {n : ℕ}
    (E : Fin (n+1) → A) : Fin (n+1) → A :=
  Fin.cases (E 0) (fun i => E i.succ - E i.castSucc)

theorem triangular_span {A : Type*} [CommRing A] {n : ℕ} (E : Fin (n+1) → A) :
    Ideal.span (Set.range (triangularDifferences E)) = Ideal.span (Set.range E) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Ideal.subset_span ⟨0,rfl⟩
    · exact (Ideal.span (Set.range E)).sub_mem (Ideal.subset_span ⟨j.succ,rfl⟩)
        (Ideal.subset_span ⟨j.castSucc,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    induction i using Fin.induction with
    | zero => exact Ideal.subset_span ⟨0,rfl⟩
    | succ i hi =>
        have hd : triangularDifferences E i.succ ∈
            Ideal.span (Set.range (triangularDifferences E)) := Ideal.subset_span ⟨i.succ,rfl⟩
        have h := (Ideal.span (Set.range (triangularDifferences E))).add_mem hd hi
        simpa [triangularDifferences] using h

noncomputable def cumulativeRelease {τ A : Type*} [CommRing A]
    (F : A) (rates : τ → Aˣ) (j : τ) : MvPolynomial τ A := C F - C (rates j : A)*X j

theorem release_span_graph {τ A : Type*} [CommRing A] (F : A) (rates : τ → Aˣ) :
    Ideal.span (Set.range (cumulativeRelease F rates)) =
      Ideal.span (Set.range (fun j : τ => X j - C (F * (↑(rates j)⁻¹ : A)))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have h := (Ideal.span (Set.range (fun j : τ => X j - C (F * (↑(rates j)⁻¹ : A))))).mul_mem_left
      (-C (rates j : A)) (Ideal.subset_span ⟨j,rfl⟩)
    convert h using 1
    simp only [cumulativeRelease,map_mul]
    have hu : C (rates j : A) * C (↑(rates j)⁻¹ : A) = (1 : MvPolynomial τ A) := by
      rw [← map_mul,Units.mul_inv,map_one]
    linear_combination -(C F) * hu
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    have h := (Ideal.span (Set.range (cumulativeRelease F rates))).mul_mem_left
      (-C (↑(rates j)⁻¹ : A)) (Ideal.subset_span ⟨j,rfl⟩)
    convert h using 1
    simp only [cumulativeRelease,map_mul]
    have hu : C (rates j : A) * C (↑(rates j)⁻¹ : A) = (1 : MvPolynomial τ A) := by
      rw [← map_mul,Units.mul_inv,map_one]
    linear_combination -(X j) * hu

end ACRZeroDivisors

import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace ACRZeroDivisors

/-- The algebraic end of the regular-point argument. No geometric premise is
axiomatized: associated-prime membership is the explicit conventional input. -/
theorem associated_prime_torsion {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) (hP : P ∈ associatedPrimes R (R ⧸ I))
    (a : R) (ha : a ∈ P) : ∃ h : R, h ∉ I ∧ a*h ∈ I := by
  have hm : a ∈ ⋃ p ∈ associatedPrimes R (R ⧸ I), (p : Set R) :=
    Set.mem_iUnion₂_of_mem hP ha
  rw [biUnion_associatedPrimes_eq_zero_divisors] at hm
  obtain ⟨x, hx, hax⟩ := hm
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨h, ?_, ?_⟩
  · intro hmem
    apply hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  · rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem] at hax
    exact hax

end ACRZeroDivisors

import proofs.IrrRAFEnumeration.SATLibraryAdapterSpec
import proofs.Complexitylib.Asymptotics

namespace IrrRAFEnumeration.SATSource
open Complexity SAT

/-- The known no-instance budget counts source and complete baseline bits. -/
theorem raw_source_and_baseline_bound (φ : CNF) :
    (sourceBits (libraryRect φ (φ.encode.length+2))).length +
      (baselineBits (φ.encode.length+2) φ.length).length ≤ 8160*(φ.encode.length+2)^4 := by
  have hm := libraryCNF_clause_count_bound φ
  have hd : φ.encode.length+2+φ.length+1 ≤ 2*(φ.encode.length+2) := by omega
  have hs := sourceBits_polynomial (libraryRect φ (φ.encode.length+2))
  have hb := baselineBits_polynomial (φ.encode.length+2) φ.length
  have h4 := Nat.pow_le_pow_left hd 4
  have h3 := Nat.pow_le_pow_left hd 3
  have h34 := Nat.pow_le_pow_right (show 1 ≤ φ.encode.length+2 by omega) (by decide : 3 ≤ 4)
  have e4 : (2*(φ.encode.length+2))^4 = 16*(φ.encode.length+2)^4 := by ring
  have e3 : (2*(φ.encode.length+2))^3 = 8*(φ.encode.length+2)^3 := by ring
  rw [e4] at h4
  rw [e3] at h3
  nlinarith

noncomputable def sourceDeadline (p : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 3000000000000000*(Polynomial.X+Polynomial.C 2)^10 +
    p.comp (Polynomial.C 8160*(Polynomial.X+Polynomial.C 2)^4)

theorem sourceDeadline_eval (p : Polynomial Nat) (L : Nat) :
    (sourceDeadline p).eval L = 3000000000000000*(L+2)^10+p.eval (8160*(L+2)^4) := by
  simp only [sourceDeadline,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_comp]

/-- Composition overhead, source construction and an output-polynomial
enumerator's complete-baseline cost are dominated by one explicit clock. -/
theorem composed_no_case_deadline (p : Polynomial Nat) (φ : CNF) :
    2*(1000000000000000*(φ.encode.length+2)^10)+
      2*(sourceBits (libraryRect φ (φ.encode.length+2))).length+11+
      p.eval ((sourceBits (libraryRect φ (φ.encode.length+2))).length+
        (baselineBits (φ.encode.length+2) φ.length).length) ≤
      (sourceDeadline p).eval φ.encode.length := by
  rw [sourceDeadline_eval]
  have hb := raw_source_and_baseline_bound φ
  have hp := polynomial_eval_mono_nat p hb
  have h4 := Nat.pow_le_pow_right (show 1 ≤ φ.encode.length+2 by omega) (by decide : 4 ≤ 10)
  have h10 : 1 ≤ (φ.encode.length+2)^10 := one_le_pow₀ (show 1 ≤ φ.encode.length+2 by omega)
  nlinarith

end IrrRAFEnumeration.SATSource

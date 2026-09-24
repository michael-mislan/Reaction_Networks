import proofs.IrrRAFEnumeration.SATLibraryAdapter

namespace IrrRAFEnumeration.SATSource

open SATCompletion Complexity

theorem libraryCNF_clause_count_bound (φ : SAT.CNF) : φ.length ≤ φ.encode.length := by
  induction φ with
  | nil => simp [SAT.CNF.encode]
  | cons c cs ih =>
    simp only [SAT.CNF.encode_cons, List.length_append, List.length_cons,
      List.length_nil] at *
    omega

theorem libraryRectangle_length_bound (φ : SAT.CNF) :
    (libraryRectangle φ).length ≤ 4*(φ.encode.length+2)^2 := by
  have hm := libraryCNF_clause_count_bound φ
  have hp := Nat.mul_le_mul_right ((φ.encode.length+2)*2) hm
  rw [libraryRectangle, cnfBits_length]
  nlinarith

theorem libraryCNF_decode_language {z : List Bool} {φ : SAT.CNF}
    (hd : SAT.CNF.decode? z = some φ) : z ∈ SAT.language ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨ψ, hz, hψ⟩
    have he : ψ = φ := by
      rw [hz, SAT.CNF.decode?_encode] at hd
      exact Option.some.inj hd
    simpa [he] using hψ
  · intro hφ
    exact ⟨φ, SAT.CNF.decode?_sound hd, hφ⟩

/-- Every raw string is mapped to a well-formed padded rectangle with exactly
the SAT-language semantics. This theorem does not assert machine runtime. -/
theorem librarySATAdapter_spec (z : List Bool) :
    ∃ (n m : Nat) (Φ : Fin m → Finset (Choice n)),
      2 ≤ n ∧ librarySATAdapter z = cnfBits Φ ∧
      ((∃ f, Satisfies Φ f) ↔ z ∈ SAT.language) := by
  cases hd : SAT.CNF.decode? z with
  | some φ =>
    refine ⟨φ.encode.length+2, φ.length, libraryRect φ _, by omega, ?_, ?_⟩
    · simp [librarySATAdapter, hd, libraryRectangle]
    · exact (libraryRect_encode_satisfiable φ).trans (libraryCNF_decode_language hd).symm
  | none =>
    refine ⟨2, 1, fun _ => ∅, by decide, ?_, ?_⟩
    · simp [librarySATAdapter, hd]
    · constructor
      · rintro ⟨f, hf⟩
        obtain ⟨x, hx, _⟩ := hf (0 : Fin 1)
        exact False.elim (Finset.notMem_empty x hx)
      · rintro ⟨φ, hz, _⟩
        rw [hz, SAT.CNF.decode?_encode] at hd
        contradiction

theorem librarySATAdapter_length_bound (z : List Bool) :
    (librarySATAdapter z).length ≤ 4*(z.length+2)^2 := by
  cases hd : SAT.CNF.decode? z with
  | some φ =>
    have hz := SAT.CNF.decode?_sound hd
    simpa [librarySATAdapter, hd, hz] using libraryRectangle_length_bound φ
  | none =>
    simp only [librarySATAdapter, hd, cnfBits_length]
    nlinarith [Nat.zero_le z.length]

end IrrRAFEnumeration.SATSource

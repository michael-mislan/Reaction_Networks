import proofs.RAFQueryCompilation.RankedExistence

namespace RAFSupportSelection
open RAF RAF.Frankl RAFQueryCompilation

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Preserve the effective survivor parents. The ambient certificate contract permits
irrelevant parents outside its baseline, so these are explicitly projected away. -/
theorem survivor_extension (Q : CRS M R) (cats : R → Finset M)
    (S T : Finset R) (hTS : T ⊆ S)
    (pT : R → Finset R) (rT : R → ℕ)
    (hT : RankedSupport Q cats T pT rT)
    (hS : ∀ r ∈ S, Supported Q (fun x r => x ∈ cats r) S r) :
    ∃ p : R → Finset R, ∃ rank : R → ℕ,
      RankedSupport Q cats S p rank ∧
      (∀ r ∈ T, p r = pT r ∩ T ∧ rank r = rT r) ∧
      (∀ r ∈ T, p r ⊆ T) := by
  classical
  obtain ⟨rS, hS⟩ := supported_ranked_exists Q cats S hS
  let b := T.sup rT + 1
  let p : R → Finset R := fun r => if r ∈ T then pT r ∩ T else S
  let rank : R → ℕ := fun r => if r ∈ T then rT r else b + rS r
  have low (r : R) (hr : r ∈ T) : rT r < b := by
    have hh : rT r ≤ T.sup rT := Finset.le_sup hr
    dsimp [b]
    omega
  refine ⟨p, rank, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr x hx
    by_cases ht : r ∈ T
    · rcases hT.1 r ht x hx with hf | ⟨t, htT, htp, hlt, hout⟩
      · exact Or.inl hf
      · exact Or.inr ⟨t, hTS htT, by simp [p, ht, htp, htT],
          by simpa [rank, htT, ht] using hlt, hout⟩
    · rcases hS.1 r hr x hx with hf | ⟨t, htS, _, hlt, hout⟩
      · exact Or.inl hf
      · refine Or.inr ⟨t, htS, by simpa [p, ht] using htS, ?_, hout⟩
        by_cases htT : t ∈ T
        · have hh := low t htT
          simp only [rank, if_pos htT, if_neg ht]
          omega
        · simp only [rank, if_neg htT, if_neg ht]
          omega
  · intro r hr
    by_cases ht : r ∈ T
    · obtain ⟨x, hc, hf | ⟨t, htT, htp, hout⟩⟩ := hT.2 r ht
      · exact ⟨x, hc, Or.inl hf⟩
      · exact ⟨x, hc, Or.inr ⟨t, hTS htT, by simp [p, ht, htp, htT], hout⟩⟩
    · obtain ⟨x, hc, hf | ⟨t, htS, _, hout⟩⟩ := hS.2 r hr
      · exact ⟨x, hc, Or.inl hf⟩
      · exact ⟨x, hc, Or.inr ⟨t, htS, by simpa [p, ht] using htS, hout⟩⟩
  · intro r hr
    simp [p, rank, hr]
  · intro r hr
    simp [p, hr]

end RAFSupportSelection

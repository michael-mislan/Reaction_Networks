import proofs.RAFQueryCompilation.RankedWitness

namespace RAFQueryCompilation
open RAF RAF.Frankl

variable {M R : Type*} [DecidableEq M] [DecidableEq R]

/-- Earliest reactant-generation stages supply ranks, including for catalytic cycles. -/
theorem supported_ranked_exists (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (hs : ∀ r ∈ S, Supported Q (fun x r => x ∈ cats r) S r) :
    ∃ rank : R → ℕ, RankedSupport Q cats S (fun _ => S) rank := by
  classical
  let rank : R → ℕ := fun r => if hr : r ∈ S then Nat.find (hs r hr).1 else 0
  have hmin (r : R) (hr : r ∈ S) (k : ℕ) (hk : Q.inputs r ⊆ closureAt Q S k) :
      rank r ≤ k := by
    simp only [rank, dif_pos hr]
    exact Nat.find_min' (hs r hr).1 hk
  have hgen (r : R) (hr : r ∈ S) : Q.inputs r ⊆ closureAt Q S (rank r) := by
    simp only [rank, dif_pos hr]
    exact Nat.find_spec (hs r hr).1
  have producer : ∀ k x, x ∈ closureAt Q S k → x ∈ Q.food ∨
      ∃ p ∈ S, rank p < k ∧ x ∈ Q.outputs p := by
    intro k
    induction k with
    | zero => intro x hx; exact Or.inl hx
    | succ k ih =>
      intro x hx
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hx
      rcases hx with hold | ⟨p, hp, hout⟩
      · rcases ih x hold with hf | ⟨p, hp, hlt, hout⟩
        · exact Or.inl hf
        · exact Or.inr ⟨p, hp, Nat.lt_succ_of_lt hlt, hout⟩
      · by_cases he : Enabled Q (closureAt Q S k) p
        · have hxout : x ∈ Q.outputs p := by simpa [he] using hout
          exact Or.inr ⟨p, hp, Nat.lt_succ_of_le (hmin p hp k he), hxout⟩
        · simp [he] at hout
  refine ⟨rank, ?_⟩
  constructor
  · intro r hr x hx
    rcases producer (rank r) x (hgen r hr hx) with hf | ⟨p, hp, hlt, hout⟩
    · exact Or.inl hf
    · exact Or.inr ⟨p, hp, hp, hlt, hout⟩
  · intro r hr
    obtain ⟨x, k, hx, hcat⟩ := (hs r hr).2
    refine ⟨x, hcat, ?_⟩
    rcases producer k x hx with hf | ⟨p, hp, _, hout⟩
    · exact Or.inl hf
    · exact Or.inr ⟨p, hp, hp, hout⟩

theorem raf_ranked_exists (Q : CRS M R) (cats : R → Finset M) (S : Finset R)
    (hs : IsRAF Q (fun x r => x ∈ cats r) S) :
    ∃ rank : R → ℕ, RankedSupport Q cats S (fun _ => S) rank :=
  supported_ranked_exists Q cats S (fun r hr => ⟨hs.2.1 r hr, hs.2.2 r hr⟩)

end RAFQueryCompilation

import proofs.CompositionalMemory.PhysicalResources
import proofs.HeritableCompositions.Branching

namespace CompositionalMemory
open FiniteCopy HeritableCompositions

/-- A depth-G family has 2^G-1 division opportunities, unlike a G-step lineage. -/
theorem whole_family_bound_all_errors {α : Type*} [Fintype α]
    (K : α → FiniteLaw (Option (α × α))) (ε : ℝ) (hε : 0 ≤ ε)
    (hK : ∀ n, (K n).mass none ≤ ε) (G : ℕ) (n : α) :
    1-((2^G-1 : ℕ) : ℝ)*ε ≤ familyFidelity K G n := by
  by_cases hε1 : ε ≤ 1
  · exact whole_family_union_bound K ε hε hε1 hK G n
  · cases G with
    | zero => simp [familyFidelity]
    | succ G =>
      have hp : 1 ≤ 2^G := Nat.one_le_pow G 2 (by norm_num)
      have hc : 1 ≤ 2^(G+1)-1 := by rw [pow_succ]; omega
      have hcr : (1 : ℝ) ≤ ((2^(G+1)-1 : ℕ) : ℝ) := by exact_mod_cast hc
      have he : 1 ≤ ((2^(G+1)-1 : ℕ) : ℝ)*ε :=
        le_trans (by simpa using hcr) (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hε1)) (by positivity))
      exact (sub_nonpos.mpr he).trans (familyFidelity_nonneg K (G+1) n)

theorem source_word_family {k : ℕ} (hk : 1 ≤ k) (N : ℕ)
    (hlarge : scalingCopyFloor ≤ N) (γ κ : ℝ) (hγ : 0 < γ)
    (hγmax : γ ≤ 1/100000000000) (hκ : 0 ≤ κ) (hκmax : κ ≤ 1/100000000000)
    (σ : Fin k → Bool) (w : Fin k → Fin k → ℝ)
    (hdiag : ∀ j, w j j=0) (hsym : ∀ j l, w j l=w l j)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j ≤ κ) :
    ∃ K : WordBirthCount N (sourceWordCenter σ) σ →
        FiniteLaw (WordBirthOutcome N (sourceWordCenter σ) σ),
      ∀ (G : ℕ) n,
        1-((2^G-1 : ℕ) : ℝ)*((k : ℝ)*scalingPrefactor γ*Real.exp (-(N : ℝ)*scalingExponent)) ≤ familyFidelity K G n := by
  obtain ⟨hN,q₀,q₁,hq₀,hq₁,hc₀,hc₁,hupper⟩ :=
    source_generation_clocks hk N hlarge γ κ hγ hγmax hκ hκmax σ w hdiag hsym hw hrow
  refine ⟨wordGenerationLaw hk γ hγ w hw N hN (sourceWordCenter σ) (sourceWordCenter_upper σ)
    σ q₀ q₁ hq₀ hq₁ hc₀ hc₁,?_⟩
  intro G n
  exact whole_family_bound_all_errors _ _ (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg k) (scalingPrefactor_pos γ hγ).le) (Real.exp_pos _).le) hupper G n

end CompositionalMemory

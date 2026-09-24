import proofs.FutileCycle.Source

namespace FutileCycle

set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

abbrev PositiveIndex (n : ℕ) := Fin (2*n-1+1) ⊕ Unit

/-- Cycle order F,S₁,C₁,S₂,C₂,…,Sₙ, with D₁ as the extra leaf. -/
def positiveSpecies (n : ℕ) (hn : 2 ≤ n) : PositiveIndex n →
    Species (Fin (n+1)) Bool (Bool × Fin n)
  | .inl i =>
    if i.val=0 then .inr (.inl true)
    else if i.val%2=1 then .inl ⟨(i.val+1)/2, by omega⟩
    else .inr (.inr (false, ⟨i.val/2, by omega⟩))
  | .inr _ => .inr (.inr (true, ⟨0, by omega⟩))

def positiveReactions (n : ℕ) (hn : 2 ≤ n) : PositiveIndex n → Reaction (Bool × Fin n)
  | .inl i =>
    if i.val=0 then ((true,⟨0, by omega⟩),.bind)
    else if i.val%2=1 then
      if hlast : i.val=2*n-1 then ((true,⟨n-1, by omega⟩),.bind)
      else ((false,⟨(i.val+1)/2, by omega⟩),.bind)
    else ((false,⟨i.val/2, by omega⟩),.convert)
  | .inr _ => ((true,⟨0, by omega⟩),.convert)

theorem positiveSpecies_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (positiveSpecies n hn) := by
  rintro (i|i) (j|j) h
  · apply congrArg Sum.inl
    apply Fin.ext
    simp only [positiveSpecies] at h
    split_ifs at h <;> simp_all only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, Prod.mk.injEq, Fin.mk.injEq, true_and] <;> omega
  · simp only [positiveSpecies] at h
    split_ifs at h <;> simp_all
  · simp only [positiveSpecies] at h
    split_ifs at h <;> simp_all
  · cases i; cases j; rfl

theorem positiveReactions_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (positiveReactions n hn) := by
  rintro (i|i) (j|j) h
  · apply congrArg Sum.inl
    apply Fin.ext
    simp only [positiveReactions] at h
    split_ifs at h <;> simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    all_goals first
      | omega
      | (obtain ⟨⟨h₁,h₂⟩,h₃⟩ := h; cases h₁ <;> cases h₃)
  · simp only [positiveReactions] at h
    split_ifs at h <;> simp_all
  · simp only [positiveReactions] at h
    split_ifs at h <;> simp_all
  · cases i; cases j; rfl

theorem positive_supported (n : ℕ) (hn : 2 ≤ n) (i : PositiveIndex n) :
    0 < reactant (futile n) (positiveSpecies n hn i) (positiveReactions n hn i) := by
  cases i with
  | inl i =>
    by_cases h0 : i.val=0
    · simp [positiveSpecies, positiveReactions, h0, reactant, futile]
    by_cases ho : i.val%2=1
    · by_cases hl : i.val=2*n-1
      · have hv : (i.val+1)/2=n := by omega
        simp only [positiveSpecies, positiveReactions, if_neg h0, if_pos ho,
          dif_pos hl]
        norm_num [reactant, futile, Fin.ext_iff, hv, show n-1+1=n by omega]
      · simp [positiveSpecies, positiveReactions, h0, ho, hl, reactant, futile]
    · simp [positiveSpecies, positiveReactions, h0, ho, reactant]
  | inr i => simp [positiveSpecies, positiveReactions, reactant]

def positiveChild (n : ℕ) (hn : 2 ≤ n) : Child (futile n) (PositiveIndex n) where
  species := positiveSpecies n hn
  species_injective := positiveSpecies_injective n hn
  reaction := positiveReactions n hn
  reaction_injective := positiveReactions_injective n hn
  supported := positive_supported n hn

theorem positive_dimension (n : ℕ) (hn : 2 ≤ n) : Fintype.card (PositiveIndex n) = 2*n+1 := by
  simp [PositiveIndex]
  omega

end FutileCycle



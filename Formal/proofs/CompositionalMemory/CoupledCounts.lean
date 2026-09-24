import proofs.CompositionalMemory.EffectiveResident
import proofs.FiniteCopy.CountSource
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

namespace CompositionalMemory
open FiniteCopy

abbrev ModularCountState (k : ℕ) := (Fin k → Counts) × ℕ
abbrev ModularChannel (k : ℕ) := (Fin k × Fin 13) ⊕ ((Fin k × Fin k) ⊕ Fin k)

def modularNext {k : ℕ} (s : ModularCountState k) : ModularChannel k → ModularCountState k
  | .inl (i,r) => (Function.update s.1 i (nextCounts (s.1 i) r),s.2)
  | .inr (.inl (i,j)) => if i=j then s else
      (Function.update (Function.update s.1 i (Function.update (s.1 i) 2 (s.1 i 2-1)))
        j (Function.update (s.1 j) 2 (s.1 j 2+1)),s.2)
  | .inr (.inr i) => (Function.update s.1 i (Function.update (s.1 i) 2 (s.1 i 2-1)),s.2+1)

noncomputable def modularRate {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) : ModularChannel k → ℝ
  | .inl (i,r) => ((s.2 : ℝ)/k)*densityRates (1/100000) (1/((s.2 : ℝ)/k))
      (effectiveConcentration ((s.2 : ℝ)/k) (s.1 i)) r
  | .inr (.inl (i,j)) => w i j*(s.1 i 2 : ℝ)
  | .inr (.inr i) => γ*(s.1 i 2 : ℝ)

/-- Rates are in tau=t/k; this definition exposes the physical clock. -/
noncomputable def physicalModularRate {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (s : ModularCountState k) (r : ModularChannel k) : ℝ := modularRate γ w s r/k

noncomputable def modularGenerator {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (f : ModularCountState k → ℝ) (s : ModularCountState k) : ℝ :=
  ∑ r, modularRate γ w s r*(f (modularNext s r)-f s)

theorem modular_rate_nonnegative {k : ℕ} (γ : ℝ) (w : Fin k → Fin k → ℝ)
    (hγ : 0 ≤ γ) (hw : ∀ i j, 0 ≤ w i j) (s : ModularCountState k) (r : ModularChannel k) :
    0 ≤ modularRate γ w s r := by
  rcases r with ⟨i,r⟩ | ⟨i,j⟩ | i
  · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (effective_rates_nonneg _ (by norm_num) _ (by positivity) (s.1 i) r)
  · exact mul_nonneg (hw i j) (Nat.cast_nonneg _)
  · exact mul_nonneg hγ (Nat.cast_nonneg _)

theorem modular_membrane_range {k : ℕ} (N : ℕ) (s : ModularCountState k)
    (hlo : k*N ≤ s.2) (hhi : s.2 < 2*(k*N)) (r : ModularChannel k) :
    k*N ≤ (modularNext s r).2 ∧ (modularNext s r).2 ≤ 2*(k*N) := by
  rcases r with ⟨i,r⟩ | ⟨i,j⟩ | i
  · simpa [modularNext] using And.intro hlo hhi.le
  · by_cases h : i=j <;> simp [modularNext,h] <;> omega
  · simp only [modularNext]; omega

theorem effective_concentration_next (v : ℝ) (n : Counts) (r : Fin 13) (h : reactants n r) :
    effectiveConcentration v (nextCounts n r) = fun i => effectiveConcentration v n i+jump r i/v := by
  funext i
  dsimp [effectiveConcentration]
  rw [nextCounts_cast n r h]
  ring

theorem effective_disabled_density (e v : ℝ) (n : Counts) (r : Fin 13)
    (h : ¬reactants n r) : densityRates e (1/v) (effectiveConcentration v n) r = 0 := by
  fin_cases r <;> norm_num [reactants] at h
  · have hn : n 0=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 1=0 ∨ n 2=0 := by omega
    rcases hn with hn | hn <;> simp [densityRates,effectiveConcentration,hn]
  · have hn : n 2=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 3=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 3=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 2=0 ∨ n 2=1 := by omega
    rcases hn with hn | hn <;> simp [densityRates,effectiveConcentration,hn]
  · have hn : n 0=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 1=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 1=0 := by omega
    simp [densityRates,effectiveConcentration,hn]
  · have hn : n 0=0 ∨ n 0=1 := by omega
    rcases hn with hn | hn <;> simp [densityRates,effectiveConcentration,hn]
  · have hn : n 3=0 := by omega
    simp [densityRates,effectiveConcentration,hn]

theorem consuming_count_cast (n : Counts) (hn : 1 ≤ n 2) (a : Fin 4) :
    ((Function.update n 2 (n 2-1)) a : ℝ) = (n a : ℝ)-(if a=2 then 1 else 0) := by
  by_cases h : a=2
  · subst a
    simp [Nat.cast_sub hn]
  · simp [h]

theorem receiving_count_cast (n : Counts) (a : Fin 4) :
    ((Function.update n 2 (n 2+1)) a : ℝ) = (n a : ℝ)+(if a=2 then 1 else 0) := by
  by_cases h : a=2
  · subst a; simp
  · simp [h]

theorem consuming_effective_concentration (v : ℝ) (n : Counts) (hn : 1 ≤ n 2) :
    effectiveConcentration v (Function.update n 2 (n 2-1)) =
      fun a => effectiveConcentration v n a+(if a=2 then (-1 : ℝ) else 0)/v := by
  funext a
  dsimp [effectiveConcentration]
  rw [consuming_count_cast n hn a]
  split_ifs <;> ring

theorem receiving_effective_concentration (v : ℝ) (n : Counts) :
    effectiveConcentration v (Function.update n 2 (n 2+1)) =
      fun a => effectiveConcentration v n a+(if a=2 then (1 : ℝ) else 0)/v := by
  funext a
  dsimp [effectiveConcentration]
  rw [receiving_count_cast]
  ring

end CompositionalMemory

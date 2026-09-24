import proofs.CompositionalMemory.SemenovCountSource
import proofs.CompositionalMemory.CenteredInventory

namespace CompositionalMemory.Semenov

theorem stoichiometric_requirements (r : Fin 11) (j : Fin 8) :
    (stoich r j).toNat ≤ 1 ∧ (-(stoich r j)).toNat ≤ 1 ∧
      (0 < (-(stoich r j)).toNat → j=reactantA r ∨ (r.val ≠ 7 ∧ j=reactantB r)) := by
  exact (by decide : ∀ r : Fin 11,∀ j : Fin 8,
    (stoich r j).toNat ≤ 1 ∧ (-(stoich r j)).toNat ≤ 1 ∧
      (0 < (-(stoich r j)).toNat → j=reactantA r ∨ (r.val ≠ 7 ∧ j=reactantB r))) r j

theorem raw_chemical_next_upper (n : Fin 8 → ℕ) (r : Fin 11) (j : Fin 8) :
    rawChemicalNext n r j ≤ n j+1 := by
  have hh := (stoichiometric_requirements r j).1
  unfold rawChemicalNext
  omega

theorem raw_chemical_next_cast (n : Fin 8 → ℕ) (r : Fin 11)
    (hA : 0 < n (reactantA r)) (hB : r.val ≠ 7 → 0 < n (reactantB r)) (j : Fin 8) :
    (rawChemicalNext n r j : ℝ)=(n j : ℝ)+(stoich r j : ℝ) := by
  have hr := stoichiometric_requirements r j
  have hsub : (-(stoich r j)).toNat ≤ n j+(stoich r j).toNat := by
    by_cases hz : (-(stoich r j)).toNat=0
    · omega
    · rcases hr.2.2 (by omega) with h | ⟨h7,h⟩
      · rw [h]
        have h1 := (stoichiometric_requirements r (reactantA r)).2.1
        omega
      · rw [h]
        have h1 := (stoichiometric_requirements r (reactantB r)).2.1
        have h2 := hB h7
        omega
  have hi : ((stoich r j).toNat : ℤ)-((-(stoich r j)).toNat : ℤ)=stoich r j := by omega
  have he : ((stoich r j).toNat : ℝ)-((-(stoich r j)).toNat : ℝ)=(stoich r j : ℝ) := by exact_mod_cast hi
  rw [rawChemicalNext,Nat.cast_sub hsub,Nat.cast_add]
  linarith only [he]

theorem positive_chemical_rate_requirements (volume : ℝ) {B K : ℕ}
    (n : Fin 8 → Fin (B+1)) (c : Fin K) (r : Fin 11)
    (hrate : 0 < reactorRate volume (some (n,c)) (Sum.inl r)) :
    0 < (n (reactantA r)).val ∧ (r.val ≠ 7 → 0 < (n (reactantB r)).val) := by
  constructor
  · by_contra h
    have hz : (n (reactantA r)).val=0 := by omega
    by_cases h7 : r.val=7 <;> simp [reactorRate,h7,hz] at hrate
  · intro h7
    by_contra h
    have hz : (n (reactantB r)).val=0 := by omega
    simp [reactorRate,h7,hz] at hrate

/-- Failed states carry combined energy one. The chemical part is not
individually clipped, so feed exhaustion cannot create a false chemical jump. -/
noncomputable def reactorCombinedEnergy {B K : ℕ} (E : (Fin 8 → ℕ) → ℝ)
    (m0 rate t : ℝ) : ReactorState B K → ℝ
  | none => 1
  | some (n,c) => E (fun j => (n j).val)+centeredInventory (K : ℝ) m0 rate t c.val

theorem reactor_combined_energy_nonneg {B K : ℕ} (E : (Fin 8 → ℕ) → ℝ)
    (hE : ∀ n,0 ≤ E n) (m0 rate t : ℝ) (s : ReactorState B K) :
    0 ≤ reactorCombinedEnergy E m0 rate t s := by
  cases s with
  | none => norm_num [reactorCombinedEnergy]
  | some p => exact add_nonneg (hE _) (centeredInventory_nonneg _ _ _ _ _)

theorem encoded_combined_energy_upper (B K : ℕ) (hK : 0 < K)
    (E : (Fin 8 → ℕ) → ℝ) (m0 rate t : ℝ) (n : Fin 8 → ℕ) (c : ℕ)
    (hE : 0 ≤ E n) (hcoord : c < K → ∀ j,n j ≤ B) (hm : m0+rate*t ≤ (K : ℝ)/2) :
    reactorCombinedEnergy E m0 rate t (encodeReactor B K n c) ≤
      E n+centeredInventory (K : ℝ) m0 rate t c := by
  unfold encodeReactor
  split_ifs with hc
  · exact le_rfl
  · have hcount : K ≤ c := by
      by_contra h
      have hlt : c < K := by omega
      exact hc ⟨hcoord hlt,hlt⟩
    have hh := centeredInventory_exhausted (K : ℝ) m0 rate t c
      (by exact_mod_cast hK) (by exact_mod_cast hcount) hm
    change 1 ≤ E n+centeredInventory (K : ℝ) m0 rate t c
    linarith only [hh,hE]

end CompositionalMemory.Semenov

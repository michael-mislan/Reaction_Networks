import proofs.CompositionalMemory.ReversibleReservoirBudget

namespace CompositionalMemory

/-- The passive tag preserves the physical reaction map on every event with
positive propensity. Disabled self-loop conventions need not coincide. -/
theorem reversiblePhysical_next_projects (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (s : ReversiblePhysicalState N) (r : ReversiblePhysicalChannel)
    (hp : 0 < reversiblePhysicalReactionRate N ε ρ s r) :
    reversiblePhysicalCounts N (reversiblePhysicalReactionNext N s r)=
      reversibleRawNext N (reversiblePhysicalCounts N s) r := by
  cases s with
  | inr s => rfl
  | inl s =>
    rcases s with ⟨j,a⟩
    have hj : j.val≠N := by
      intro he
      have hz : reversiblePhysicalReactionRate N ε ρ (.inl (j,a)) r=0 := by
        simp [reversiblePhysicalReactionRate,reversibleRawRate,reversiblePhysicalCounts,he,two_mul]
      rw [hz] at hp
      exact lt_irrefl _ hp
    have hn : N≠0 := Nat.ne_of_gt hN
    have hm2 : N+j.val≠2*N := by omega
    rcases r with ⟨k,r⟩
    have hg (hr : r.val=5) : (a k).1≠0 := by
      intro hx
      have he : r=5 := Fin.ext hr
      have hz : reversiblePhysicalReactionRate N ε ρ (.inl (j,a)) (k,r)=0 := by
        simp [reversiblePhysicalReactionRate,reversibleRawRate,reversiblePhysicalCounts,he,hx]
      rw [hz] at hp
      exact lt_irrefl _ hp
    fin_cases r <;>
      simp [reversiblePhysicalReactionNext,reversiblePhysicalCounts,reversibleCountReactionNext,
        coupledCountReactionNext,reversibleRawNext,hj,hn,hm2]
    · simp [hg rfl,Nat.add_assoc]

/-- Whenever a raw event is enabled, the membrane count changes by its
declared M stoichiometry; this is the volume input used by the controller. -/
theorem reversibleRaw_membrane_stoich (N : Nat) (ε ρ : ℝ)
    (s : Nat × (Fin 2 → Int × Int)) (r : ReversiblePhysicalChannel)
    (hp : 0 < reversibleRawRate N ε ρ s r) :
    ((reversibleRawNext N s r).1 : Int)=(s.1 : Int)+reversibleChannelStoich r.2 2 := by
  have hm0 : s.1≠0 := by
    intro he
    simp [reversibleRawRate,he] at hp
  have hm2 : s.1≠2*N := by
    intro he
    simp [reversibleRawRate,he] at hp
  rcases r with ⟨k,r⟩
  fin_cases r <;> norm_num [reversibleRawNext,reversibleChannelStoich,hm0,hm2,Matrix.cons_val_two]
  exact Int.ofNat_sub (by omega : 1 ≤ s.1)

theorem reversiblePhysical_membrane_stoich (N : Nat) (hN : 0 < N) (ε ρ : ℝ)
    (s : ReversiblePhysicalState N) (r : ReversiblePhysicalChannel)
    (hp : 0 < reversiblePhysicalReactionRate N ε ρ s r) :
    ((reversiblePhysicalCounts N (reversiblePhysicalReactionNext N s r)).1 : Int)=
      ((reversiblePhysicalCounts N s).1 : Int)+reversibleChannelStoich r.2 2 := by
  rw [reversiblePhysical_next_projects N hN ε ρ s r hp]
  exact reversibleRaw_membrane_stoich N ε ρ (reversiblePhysicalCounts N s) r hp

end CompositionalMemory

import proofs.TypeII3.Network.SourceMembership

namespace TypeIIL

open TypeII3

/-- The two-species restriction retained when the cycle reaction immediately
before fork `i_j` is `σ_j → s i_j` and the fork is chemostatted to retain only
its coefficient-one back product `i_j → σ_j`. -/
def terminalReplicationRestriction (s : ℕ) : Fin 2 → Fin 2 → ℝ := ![
  ![-1, 1],
  ![(s : ℝ), -1]]

def terminalReplicationWitness : Fin 2 → ℝ := ![2, 3]

/-- Any terminal cycle multiplicity at least two exposes a proper
stoichiometrically autocatalytic two-species restriction. -/
theorem terminal_replication_restriction_autocatalytic
    {s : ℕ} (hs : 2 ≤ s) :
    StoichiometricallyAutocatalytic (terminalReplicationRestriction s) := by
  refine ⟨terminalReplicationWitness, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [terminalReplicationWitness]
  · intro i
    fin_cases i
    · norm_num [terminalReplicationRestriction, terminalReplicationWitness,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
    · simp [terminalReplicationRestriction, terminalReplicationWitness,
        Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
      exact_mod_cast (show 3 < s * 2 by omega)

/-- Source minimality therefore forces every cycle reaction immediately
preceding a fork to be unit stoichiometric.  This is precisely the boundary
unit used by `source_terminal_transport`; arbitrary weights may remain in the
interior of the gap. -/
theorem terminal_weight_eq_one_of_no_autocatalytic_pair
    {s : ℕ} (hs : 0 < s)
    (hminimal :
      ¬ StoichiometricallyAutocatalytic (terminalReplicationRestriction s)) :
    s = 1 := by
  by_contra hne
  have hs2 : 2 ≤ s := by omega
  exact hminimal (terminal_replication_restriction_autocatalytic hs2)

end TypeIIL

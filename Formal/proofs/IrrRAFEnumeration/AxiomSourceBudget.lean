import proofs.AllIrrRAFCert.WPHardness.Encoding

namespace IrrRAFEnumeration.AxiomSource
open AllIrrRAFCert.WPHardness

/-- Unary molecule/reaction headers plus dense incidence data and a family
of fixed-width reaction masks, each preceded by a record bit, then a terminator. -/
def sourceAndBaselineBits (k n q : Nat) :=
  encodingCells k n q + Fintype.card (Mol k n) + Fintype.card (Rxn k n q) + k + 4

private theorem numericBudget (k m q D : Nat) (hk : k ≤ D) (hm : m ≤ D)
    (hq : q ≤ D) (hD : 1 ≤ D) :
    (2+2*(k*m)+k+m) + (3*(2+2*(k*m)+k+m)+k)*(2*(k*m)+q+1) +
      (2+2*(k*m)+k+m) + (2*(k*m)+q+1) + k + 4 ≤ 120*D^4 := by
  have hprod : k*m ≤ D^2 := by
    simpa [pow_two] using Nat.mul_le_mul hk hm
  have hDsq : D ≤ D^2 := by
    simpa using (pow_le_pow_right' hD (by decide : 1 ≤ 2))
  have hM : 2+2*(k*m)+k+m ≤ 6*D^2 := by omega
  have hH : 2*(k*m)+q+1 ≤ 4*D^2 := by omega
  have hrows : (3*(2+2*(k*m)+k+m)+k)*(2*(k*m)+q+1) ≤
      (18*D^2+D)*(4*D^2) :=
    Nat.mul_le_mul (by omega) hH
  have hDcube : D^3 ≤ D^4 := by
    exact pow_le_pow_right' hD (by decide : 3 ≤ 4)
  have hDfour : D^2 ≤ D^4 := by
    exact pow_le_pow_right' hD (by decide : 2 ≤ 4)
  nlinarith only [hM,hH,hrows,hDcube,hDfour,hDsq,hk,hD]

theorem sourceAndBaselineBits_polynomial (k n q : Nat) :
    sourceAndBaselineBits k n q ≤ 120 * (k+n+q+3)^4 := by
  unfold sourceAndBaselineBits encodingCells
  rw [molecule_count, reaction_count]
  exact numericBudget k (n+2) q (k+n+q+3) (by omega) (by omega) (by omega) (by omega)

theorem smallGenerating_of_large_budget {k n q : Nat} (A : System n q)
    (hk : n+2 ≤ k) : SmallGenerating A k := by
  refine ⟨Finset.univ,?_,?_⟩
  · simpa using hk
  · intro u
    exact Derives.seed (Finset.mem_univ u)

end IrrRAFEnumeration.AxiomSource

import proofs.InheritedCellAssay.RobustSisters

namespace InheritedCellAssay
open scoped BigOperators

/-- Complete paired offspring list. The first F-k pairs are complementary;
the remaining pairs copy a fair sign selected by the founder subset. -/
noncomputable def sisterPairs (F k : ℕ) (s : Finset (Fin k)) : List (Bool × Bool) :=
  List.replicate (F-k) (true,false) ++
  s.toList.map (fun _ => (true,true)) ++
  ((Finset.univ : Finset (Fin k)) \ s).toList.map (fun _ => (false,false))

/-- Every daughter is followed for three selective generations. -/
noncomputable def sisterEndpoint (F k : ℕ) (s : Finset (Fin k)) : List Bool :=
  (sisterPairs F k s).flatMap (fun ab => descendants 3 ab.1 ++ descendants 3 ab.2)

theorem sister_endpoint_count (F k : ℕ) (s : Finset (Fin k)) :
    (sisterEndpoint F k s).length = 9*(F-k)+16*s.card+2*(k-s.card) := by
  simp [sisterEndpoint, sisterPairs, descendants, offspring,
    List.length_flatMap, Finset.card_sdiff, Nat.mul_comm, Nat.add_assoc]

theorem sister_endpoint_response (F k : ℕ) (s : Finset (Fin k)) :
    ((sisterEndpoint F k s).filter id).length = 8*(F-k)+16*s.card := by
  simp [sisterEndpoint, sisterPairs, descendants, offspring,
    List.filter_flatMap, List.length_flatMap, Nat.mul_comm]

noncomputable def sisterReadout (F k : ℕ) (s : Finset (Fin k)) : ℚ :=
  (((sisterEndpoint F k s).filter id).length : ℚ) /
    (sisterEndpoint F k s).length

theorem sister_readout_eq (F k : ℕ) (hk : k ≤ F) (s : Finset (Fin k)) :
    sisterReadout F k s = selectiveFraction (2*F) (daughterHigh F k s.card) := by
  have hc : s.card ≤ k := by simpa using Finset.card_le_univ s
  have hr : 8*(F-k)+16*s.card = 8*(F-k+2*s.card) := by omega
  have hn : 9*(F-k)+16*s.card+2*(k-s.card) =
      8*(F-k+2*s.card)+(2*F-(F-k+2*s.card)) := by omega
  simp only [sisterReadout, sister_endpoint_response, sister_endpoint_count, hr, hn,
    selectiveFraction, daughterHigh, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

noncomputable def actualSisterRisk (F k : ℕ) : ℚ :=
  sourceExpectation k (fun s => if |sisterReadout F k s-8/9| > 1/10 then 1 else 0)

theorem sister_risk_transport (F k : ℕ) (hk : k ≤ F) :
    actualSisterRisk F k = conditionalRisk F k := by
  simp_rw [actualSisterRisk, sister_readout_eq F k hk]
  exact source_count_transport k (fun j =>
    if |selectiveFraction (2*F) (daughterHigh F k j)-8/9| > 1/10 then 1 else 0)

noncomputable def actualMixtureRisk (w : Fin 31 → ℚ) : ℚ :=
  ∑ k, w k * actualSisterRisk 30 k

theorem actual_mixture_transport (w : Fin 31 → ℚ) :
    actualMixtureRisk w = mixtureRisk w := by
  unfold actualMixtureRisk mixtureRisk
  apply Finset.sum_congr rfl
  intro k _
  rw [sister_risk_transport 30 k (by omega)]

/-- Complete source-to-observation uniform error guarantee, including unknown
mixture weights. Normalization and nonnegativity are the only weight assumptions. -/
theorem robust_resolution (w : Fin 31 → ℚ)
    (hw : ∀ k, 0 ≤ w k) (hn : ∑ k, w k = 1) :
    actualMixtureRisk w ≤ 2061197/67108864 ∧ actualMixtureRisk w < 1/20 := by
  rw [actual_mixture_transport]
  exact ⟨robust_thirty_bound w hw hn, robust_thirty_design w hw hn⟩

end InheritedCellAssay

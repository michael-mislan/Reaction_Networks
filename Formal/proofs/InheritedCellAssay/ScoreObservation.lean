import proofs.InheritedCellAssay.FiniteSource

namespace InheritedCellAssay

/-- Perfect binary copying of either state, with no selection. -/
def neutralDescendants : ℕ → Bool → List Bool
  | 0, b => [b]
  | g+1, b => neutralDescendants g b ++ neutralDescendants g b

theorem neutral_descendants (g : ℕ) (b : Bool) :
    neutralDescendants g b = List.replicate (2^g) b := by
  induction g with
  | zero => simp [neutralDescendants]
  | succ g ih => simp [neutralDescendants, ih, pow_succ, Nat.mul_two]

noncomputable def neutralEndpoint (s : Finset (Fin 10)) : List Bool :=
  s.toList.flatMap (fun _ => neutralDescendants 4 true) ++
  ((Finset.univ : Finset (Fin 10)) \ s).toList.flatMap
    (fun _ => neutralDescendants 4 false)

theorem neutral_endpoint_counts (s : Finset (Fin 10)) :
    (neutralEndpoint s).length = 160 ∧
    ((neutralEndpoint s).filter id).length = 16*s.card := by
  have hc : s.card ≤ 10 := by simpa using Finset.card_le_univ s
  constructor
  · simp [neutralEndpoint, neutral_descendants, List.length_flatMap,
      Finset.card_sdiff]
    omega
  · simp [neutralEndpoint, neutral_descendants, List.filter_flatMap,
      List.length_flatMap, Nat.mul_comm]

noncomputable def actualScoreCoverage : ℚ :=
  sourceExpectation 10 (fun s =>
    if scoreAccept ((neutralEndpoint s).length : ℚ)
      (((neutralEndpoint s).filter id).length : ℚ) (1/2) then 1 else 0)

theorem actual_score_coverage : actualScoreCoverage = 63/256 := by
  have hc (s : Finset (Fin 10)) := neutral_endpoint_counts s
  unfold actualScoreCoverage
  simp_rw [hc, Nat.cast_mul, Nat.cast_ofNat]
  exact (source_count_transport 10 (fun h =>
    if scoreAccept 160 (16*h) (1/2) then 1 else 0)).trans perfect_copy_score_coverage

end InheritedCellAssay

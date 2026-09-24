import proofs.FiniteReservoir.FiniteModel

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy

/-- The finite encoding agrees with the physical bath update on every supported label. -/
theorem fuel_next_supported (V M : ℕ) (p : Parameters M) (X : BoxState V M)
    (j : CompetitionChannel) (hj : rate (boxState X) V p.release p.cleavage p.capacity j ≠ 0) :
    bathOf (fuelNext X.2 j) = (next (boxState X) j).2 := by
  cases j with
  | inl j => rfl
  | inr j =>
    fin_cases j
    · have hf : 0 < X.2.val := by
        by_contra h
        have hz : X.2.val=0 := by omega
        apply hj
        simp [rate,boxState,bathOf,CommonPhysicalRealization.physicalRate,hz]
      have hbound := X.2.isLt
      norm_num [bathOf,fuelNext,next,boxState,Bath.forward]
      omega
    · have hf : X.2.val < M := by
        by_contra h
        have hz : M-X.2.val=0 := by omega
        apply hj
        norm_num [rate,boxState,bathOf,CommonPhysicalRealization.physicalRate,hz]
      norm_num [bathOf,fuelNext,next,boxState,Bath.reverse]
      omega

/-- The finite stopped model has the physical successor on every active, supported jump. -/
theorem box_next_supported (V M : ℕ) (p : Parameters M) (X : BoxState V M)
    (hc : resourceGood (boxCounts X.1) V) (j : CompetitionChannel)
    (hj : rate (boxState X) V p.release p.cleavage p.capacity j ≠ 0) :
    boxState (boxNext V M X j) = next (boxState X) j := by
  apply Prod.ext
  · change boxCounts (RandomViability.Binding.boxNext V X.1 (competitionBase j)) = _
    rw [boxNext_exact V X.1 (competitionBase j) hc]
    rfl
  · exact fuel_next_supported V M p X j hj

end
end FiniteReservoir
